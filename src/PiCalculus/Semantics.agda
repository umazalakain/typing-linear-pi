open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Bool.Base using (false; true)
open import Data.Product hiding (swap)
open import Relation.Nullary using (_because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

import Data.Fin as Fin
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ

open Fin using (Fin ; zero ; suc; #_)

open import PiCalculus.Syntax
open Syntax
open Scoped

module PiCalculus.Semantics where

  private
    variable
      n : ℕ
      P P' Q R : Scoped n
      x y : Fin n


  Unused : ∀ {n} → Fin n → Scoped n → Set
  Unused i 𝟘 = ⊤
  Unused i (new P) = Unused (suc i) P
  Unused i (P ∥ Q) = Unused i P × Unused i Q
  Unused i (x ⦅⦆ P) = i ≢ x × Unused (suc i) P
  Unused i (x ⟨ y ⟩ P) = i ≢ x × i ≢ y × Unused i P
  Unused i (+[] P) = Unused (suc i) P

  lift : (i : Fin (suc n)) → Scoped n → Scoped (suc n)
  lift i 𝟘 = 𝟘
  lift i (new P) = new lift (suc i) P
  lift i (P ∥ Q) = lift i P ∥ lift i Q
  lift i (x ⦅⦆ P) = Fin.punchIn i x ⦅⦆ lift (suc i) P
  lift i (x ⟨ y ⟩ P) = Fin.punchIn i x ⟨ Fin.punchIn i y ⟩ lift i P
  lift i (+[] P) = +[] lift (suc i) P

  lower : (i : Fin (suc n)) (P : Scoped (suc n)) → Unused i P → Scoped n
  lower i 𝟘 uP = 𝟘
  lower i (new P) uP = new lower (suc i) P uP
  lower i (P ∥ Q) (uP , uQ) = lower i P uP ∥ lower i Q uQ
  lower i (x ⦅⦆ P) (i≢x , uP) = Fin.punchOut i≢x ⦅⦆ lower (suc i) P uP
  lower i (x ⟨ y ⟩ P) (i≢x , (i≢y , uP)) = Fin.punchOut i≢x ⟨ Fin.punchOut i≢y ⟩ lower i P uP
  lower i (+[] P) uP = +[] lower (suc i) P uP

  swapFin : Fin n → Fin n → Fin n → Fin n
  swapFin i j x with i Finₚ.≟ x
  swapFin i j x | true because _ = j
  swapFin i j x | false because _ with j Finₚ.≟ x
  swapFin i j x | false because _ | true because _ = i
  swapFin i j x | false because _ | false because _ = x

  swap : (i j : Fin n) → Scoped n → Scoped n
  swap i j 𝟘 = 𝟘
  swap i j (new P) = new swap (suc i) (suc j) P
  swap i j (P ∥ Q) = swap i j P ∥ swap i j Q
  swap i j (x ⦅⦆ P)  = swapFin i j x ⦅⦆ swap (suc i) (suc j) P
  swap i j (x ⟨ y ⟩ P)  = swapFin i j x ⟨ swapFin i j y ⟩ swap i j P
  swap i j (+[] P) = +[] swap (suc i) (suc j) P

  infixl 10 _≈_
  data _≈_ : Scoped n → Scoped n → Set where
    comp-assoc : P ∥ (Q ∥ R) ≈ (P ∥ Q) ∥ R

    comp-symm : P ∥ Q ≈ Q ∥ P

    comp-end : P ∥ 𝟘 ≈ P

    scope-end : _≈_ {n} (new 𝟘) 𝟘

    base-end : _≈_ {n} (+[] 𝟘) 𝟘

    scope-ext : (u : Unused zero P)
              → new (P ∥ Q) ≈ lower zero P u ∥ (new Q)

    base-ext : (u : Unused zero P)
             → +[] (P ∥ Q) ≈ lower zero P u ∥ (+[] Q)

    scope-scope-comm : new (new P) ≈ new (new swap (# 0) (# 1) P)

    scope-base-comm : new (+[] P) ≈ +[] (new swap (# 0) (# 1) P)

    base-base-comm : +[] (+[] P) ≈ +[] (+[] swap (# 0) (# 1) P)

  data RecTree : Set where
    zero : RecTree
    one : RecTree → RecTree
    two : RecTree → RecTree → RecTree

  private
    variable
      r p : RecTree

  infixl 5 _≅⟨_⟩_
  data _≅⟨_⟩_ : Scoped n → RecTree → Scoped n → Set where
    stop_ : P ≈ Q → P ≅⟨ zero ⟩ Q

    -- Equivalence relation
    cong-refl  : P ≅⟨ zero ⟩ P
    cong-symm_ : P ≅⟨ r ⟩ Q → Q ≅⟨ one r ⟩ P
    cong-trans : P ≅⟨ r ⟩ Q → Q ≅⟨ p ⟩ R → P ≅⟨ two r p ⟩ R

    -- Congruent relation
    new-cong_    : P ≅⟨ r ⟩ P' → new P ≅⟨ one r ⟩ new P'
    comp-cong_   : P ≅⟨ r ⟩ P' → P ∥ Q ≅⟨ one r ⟩ P' ∥ Q
    input-cong_  : P ≅⟨ r ⟩ P' → x ⦅⦆ P ≅⟨ one r ⟩ x ⦅⦆ P'
    output-cong_ : P ≅⟨ r ⟩ P' → x ⟨ y ⟩ P ≅⟨ one r ⟩ x ⟨ y ⟩ P'
    base-cong_   : P ≅⟨ r ⟩ P' → +[] P ≅⟨ one r ⟩ +[] P'

  substFin : Fin n → Fin n → Fin n → Fin n
  substFin i j x with j Finₚ.≟ x
  substFin i j x | true because _ = i
  substFin i j x | false because _ = x

  [_/_]_ : (i j : Fin n) → Scoped n → Scoped n
  [ i / j ] 𝟘 = 𝟘
  [ i / j ] (new P) = new ([ suc i / suc j ] P)
  [ i / j ] (P ∥ Q) = ([ i / j ] P) ∥ ([ i / j ] Q)
  [ i / j ] (x ⦅⦆ P) = substFin i j x ⦅⦆ ([ suc i / suc j ] P)
  [ i / j ] (x ⟨ y ⟩ P) = substFin i j x ⟨ substFin i j y ⟩ ([ i / j ] P)
  [ i / j ] (+[] P) = +[] ([ suc i / suc j ] P)

  substFin-unused : ∀ {i j} (x : Fin (suc n)) → j ≢ i → j ≢ substFin i j x
  substFin-unused {j = j} x j≢suci  with j Finₚ.≟ x
  substFin-unused {j = j} x j≢suci | true because _ = j≢suci
  substFin-unused {j = j} x j≢suci | false because ofⁿ ¬p = ¬p

  subst-unused : {i j : Fin (suc n)}
               → j ≢ i
               → (P : Scoped (suc n))
               → Unused j ([ i / j ] P)
  subst-unused j≢suci 𝟘 = tt
  subst-unused j≢suci (new P) = subst-unused (λ j≡suci → j≢suci (Finₚ.suc-injective j≡suci)) P
  subst-unused j≢suci (P ∥ Q) = subst-unused j≢suci P , subst-unused j≢suci Q
  subst-unused j≢suci (x ⦅⦆ P) = substFin-unused x j≢suci , subst-unused (λ j≡suci → j≢suci (Finₚ.suc-injective j≡suci)) P
  subst-unused j≢suci (x ⟨ y ⟩ P) = substFin-unused x j≢suci , substFin-unused y j≢suci , subst-unused j≢suci P
  subst-unused j≢suci (+[] P) = subst-unused (λ j≡suci → j≢suci (Finₚ.suc-injective j≡suci)) P

  Channel : (n : ℕ) → Set
  Channel n = Maybe (Fin n)

  decrementChannel : Channel (suc n) → Channel n
  decrementChannel nothing = nothing
  decrementChannel (just zero) = nothing
  decrementChannel (just (suc i)) = just i

  infixl 5 _=[_]⇒_
  data _=[_]⇒_ : Scoped n → Channel n → Scoped n → Set where
    comm : ∀ {P : Scoped (1 + n)} {Q : Scoped n} {i j : Fin n}
         → let uP = subst-unused (λ ()) P in
           (i ⦅⦆ P) ∥ (i ⟨ j ⟩ Q) =[ just i ]⇒ lower zero ([ suc j / zero ] P) uP ∥ Q

    par_ : ∀ {c} {P P' Q : Scoped n}
         → P =[ c ]⇒ P'
         → P ∥ Q =[ c ]⇒ P' ∥ Q

    res_ : ∀ {c} {P Q : Scoped (1 + n)}
         → P =[ c ]⇒ Q
         → new P =[ decrementChannel c ]⇒ new Q

    intro_ : ∀ {c} {P Q : Scoped (1 + n)}
           → P =[ c ]⇒ Q
           → +[] P =[ decrementChannel c ]⇒ +[] Q

    struct : ∀ {c} {P Q P' : Scoped n}
           → P ≅⟨ r ⟩ P'
           → P' =[ c ]⇒ Q
           → P =[ c ]⇒ Q
