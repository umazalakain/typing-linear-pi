open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong)
open import Relation.Nullary using (_because_; ofʸ; ofⁿ)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base
open import Data.Bool.Base using (false; true)
open import Data.Product hiding (swap)

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

  lift : (i : Fin (suc n)) → Scoped n → Scoped (suc n)
  lift i 𝟘 = 𝟘
  lift i (new P) = new lift (suc i) P
  lift i (P ∥ Q) = lift i P ∥ lift i Q
  lift i (x ⦅⦆ P) = Fin.punchIn i x ⦅⦆ lift (suc i) P
  lift i (x ⟨ y ⟩ P) = Fin.punchIn i x ⟨ Fin.punchIn i y ⟩ lift i P

  lower : (i : Fin (suc n)) (P : Scoped (suc n)) → Unused i P → Scoped n
  lower i 𝟘 uP = 𝟘
  lower i (new P) uP = new lower (suc i) P uP
  lower i (P ∥ Q) (uP , uQ) = lower i P uP ∥ lower i Q uQ
  lower i (x ⦅⦆ P) (i≢x , uP) = Fin.punchOut i≢x ⦅⦆ lower (suc i) P uP
  lower i (x ⟨ y ⟩ P) (i≢x , (i≢y , uP)) = Fin.punchOut i≢x ⟨ Fin.punchOut i≢y ⟩ lower i P uP

  notMax : (i : Fin n) (x : Fin (suc n)) → Fin.inject₁ i ≡ x → n ≢ Fin.toℕ x
  notMax i x p n≡x = Finₚ.toℕ-inject₁-≢ i (trans n≡x (sym (cong Fin.toℕ p)))

  swapFin : Fin n → Fin (suc n) → Fin (suc n)
  swapFin i x with Fin.inject₁ i Fin.≟ x
  swapFin i x | true because ofʸ p = suc (Fin.lower₁ x (notMax i x p))
  swapFin i x | false because _ with (suc i) Fin.≟ x
  swapFin i x | false because _ | true because _ = Fin.inject₁ i
  swapFin i x | false because _ | false because _ = x

  swap : Fin n → Scoped (suc n) → Scoped (suc n)
  swap i 𝟘 = 𝟘
  swap i (new P) = new swap (suc i) P
  swap i (P ∥ Q) = swap i P ∥ swap i Q
  swap i (x ⦅⦆ P)  = swapFin i x ⦅⦆ swap (suc i) P
  swap i (x ⟨ y ⟩ P)  = swapFin i x ⟨ swapFin i y ⟩ swap i P

  infixl 10 _≈_
  data _≈_ : Scoped n → Scoped n → Set where
    comp-assoc : P ∥ (Q ∥ R) ≈ (P ∥ Q) ∥ R

    comp-symm : P ∥ Q ≈ Q ∥ P

    comp-end : P ∥ 𝟘 ≈ P

    scope-end : _≈_ {n} (new 𝟘) 𝟘

    scope-ext : (u : Unused zero P)
              → new (P ∥ Q) ≈ lower zero P u ∥ (new Q)

    scope-scope-comm : new (new P) ≈ new (new swap zero P)

  data RecTree : Set where
    zero : RecTree
    one : RecTree → RecTree
    two : RecTree → RecTree → RecTree

  private
    variable
      r p : RecTree

  -- TODO: change names as per paper
  infixl 5 _≅⟨_⟩_
  data _≅⟨_⟩_ : Scoped n → RecTree → Scoped n → Set where
    stop_ : P ≈ Q → P ≅⟨ zero ⟩ Q

    -- Equivalence relation
    cong-refl  : P ≅⟨ zero ⟩ P
    cong-symm_ : P ≅⟨ r ⟩ Q → Q ≅⟨ one r ⟩ P
    cong-trans : P ≅⟨ r ⟩ Q → Q ≅⟨ p ⟩ R → P ≅⟨ two r p ⟩ R

    -- Congruent relation
    new-cong_    : P ≅⟨ r ⟩ P' → new P     ≅⟨ one r ⟩ new P'
    comp-cong_   : P ≅⟨ r ⟩ P' → P ∥ Q     ≅⟨ one r ⟩ P' ∥ Q
    input-cong_  : P ≅⟨ r ⟩ P' → x ⦅⦆ P    ≅⟨ one r ⟩ x ⦅⦆ P'
    output-cong_ : P ≅⟨ r ⟩ P' → x ⟨ y ⟩ P ≅⟨ one r ⟩ x ⟨ y ⟩ P'

  substFin : Fin n → Fin n → Fin n → Fin n
  substFin i j x with j Finₚ.≟ x
  substFin i j x | true because _ = i
  substFin i j x | false because _ = x

  substProc : (i j : Fin n) → Scoped n → Scoped n
  substProc i j 𝟘 = 𝟘
  substProc i j (new P) = new (substProc (suc i) (suc j) P)
  substProc i j (P ∥ Q) = (substProc i j P) ∥ (substProc i j Q)
  substProc i j (x ⦅⦆ P) = substFin i j x ⦅⦆ (substProc (suc i) (suc j) P)
  substProc i j (x ⟨ y ⟩ P) = substFin i j x ⟨ substFin i j y ⟩ (substProc i j P)

  substFin-unused : ∀ {i j} (x : Fin (suc n)) → j ≢ i → j ≢ substFin i j x
  substFin-unused {j = j} x j≢suci  with j Finₚ.≟ x
  substFin-unused {j = j} x j≢suci | true because _ = j≢suci
  substFin-unused {j = j} x j≢suci | false because ofⁿ ¬p = ¬p

  subst-unused : {i j : Fin (suc n)}
               → j ≢ i
               → (P : Scoped (suc n))
               → Unused j (substProc i j P)
  subst-unused j≢suci 𝟘 = tt
  subst-unused j≢suci (new P) = subst-unused (λ j≡suci → j≢suci (Finₚ.suc-injective j≡suci)) P
  subst-unused j≢suci (P ∥ Q) = subst-unused j≢suci P , subst-unused j≢suci Q
  subst-unused j≢suci (x ⦅⦆ P) = substFin-unused x j≢suci , subst-unused (λ j≡suci → j≢suci (Finₚ.suc-injective j≡suci)) P
  subst-unused j≢suci (x ⟨ y ⟩ P) = substFin-unused x j≢suci , substFin-unused y j≢suci , subst-unused j≢suci P

  _[_/_]_ : Scoped (suc n) → (i j : Fin (suc n)) → (j≢i : j ≢ i) → Scoped n
  P [ i / j ] j≢i = lower j (substProc i j P) (subst-unused j≢i P)

  data Channel : ℕ → Set where
    internal : ∀ {n}         → Channel n
    external : ∀ {n} → Fin n → Channel n

  dec : Channel (suc n) → Channel n
  dec internal = internal
  dec (external zero) = internal
  dec (external (suc i)) = external i

  maybe : ∀ {a} {A : Set a} → A → (Fin n → A) → Channel n → A
  maybe b f internal = b
  maybe b f (external x) = f x

  infixl 5 _=[_]⇒_
  data _=[_]⇒_ : Scoped n → Channel n → Scoped n → Set where

    comm : ∀ {P : Scoped (1 + n)} {Q : Scoped n} {i j : Fin n}
         → (i ⦅⦆ P) ∥ (i ⟨ j ⟩ Q) =[ external i ]⇒ (P [ suc j / zero ] (λ ())) ∥ Q

    par_ : ∀ {c} {P P' Q : Scoped n}
         → P =[ c ]⇒ P'
         → P ∥ Q =[ c ]⇒ P' ∥ Q

    res_ : ∀ {c} {P Q : Scoped (1 + n)}
         → P =[ c ]⇒ Q
         → new P =[ dec c ]⇒ new Q

    struct : ∀ {c} {P Q P' : Scoped n}
           → P ≅⟨ r ⟩ P'
           → P' =[ c ]⇒ Q
           → P =[ c ]⇒ Q
