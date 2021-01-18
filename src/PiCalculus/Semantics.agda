{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong)
open import Relation.Nullary using (_because_; ofʸ; ofⁿ)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base
open import Data.Bool.Base using (false; true)
open import Data.Product using (_×_; _,_; ∃-syntax)

import Data.Fin as Fin
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ

open Fin using (Fin ; zero ; suc; #_)

open import PiCalculus.Syntax
open Scoped

module PiCalculus.Semantics where

  private
    variable
      name namex namey : Name
      n : ℕ
      P P' Q R : Scoped n
      x y : Fin n

  Unused : ∀ {n} → Fin n → Scoped n → Set
  Unused i 𝟘 = ⊤
  Unused i (ν P) = Unused (suc i) P
  Unused i (P ∥ Q) = Unused i P × Unused i Q
  Unused i (x ⦅⦆ P) = i ≢ x × Unused (suc i) P
  Unused i (x ⟨ y ⟩ P) = i ≢ x × i ≢ y × Unused i P

  lift : (i : Fin (suc n)) → Scoped n → Scoped (suc n)
  lift i 𝟘 = 𝟘
  lift i (ν P) = ν (lift (suc i) P)
  lift i (P ∥ Q) = lift i P ∥ lift i Q
  lift i (x ⦅⦆ P) = Fin.punchIn i x ⦅⦆ lift (suc i) P
  lift i (x ⟨ y ⟩ P) = Fin.punchIn i x ⟨ Fin.punchIn i y ⟩ lift i P

  lower : (i : Fin (suc n)) (P : Scoped (suc n)) → Unused i P → Scoped n
  lower i 𝟘 uP = 𝟘
  lower i (ν P) uP = ν (lower (suc i) P uP)
  lower i (P ∥ Q) (uP , uQ) = lower i P uP ∥ lower i Q uQ
  lower i (x ⦅⦆ P) (i≢x , uP) = Fin.punchOut i≢x ⦅⦆ lower (suc i) P uP
  lower i (x ⟨ y ⟩ P) (i≢x , (i≢y , uP)) = Fin.punchOut i≢x ⟨ Fin.punchOut i≢y ⟩ lower i P uP

  notMax : (i : Fin n) (x : Fin (suc n)) → Fin.inject₁ i ≡ x → n ≢ Fin.toℕ x
  notMax i x p n≡x = Finₚ.toℕ-inject₁-≢ i (trans n≡x (sym (cong Fin.toℕ p)))

  exchangeFin : Fin n → Fin (suc n) → Fin (suc n)
  exchangeFin i x with Fin.inject₁ i Fin.≟ x
  exchangeFin i x | true because ofʸ p = suc (Fin.lower₁ x (notMax i x p))
  exchangeFin i x | false because _ with (suc i) Fin.≟ x
  exchangeFin i x | false because _ | true because _ = Fin.inject₁ i
  exchangeFin i x | false because _ | false because _ = x

  exchange : Fin n → Scoped (suc n) → Scoped (suc n)
  exchange i 𝟘 = 𝟘
  exchange i (ν P) = ν (exchange (suc i) P)
  exchange i (P ∥ Q) = exchange i P ∥ exchange i Q
  exchange i (x ⦅⦆ P)  = exchangeFin i x ⦅⦆ exchange (suc i) P
  exchange i (x ⟨ y ⟩ P)  = exchangeFin i x ⟨ exchangeFin i y ⟩ exchange i P

  infixl 10 _≈_
  data _≈_ : Scoped n → Scoped n → Set where
    comp-assoc : P ∥ (Q ∥ R) ≈ (P ∥ Q) ∥ R

    comp-symm : P ∥ Q ≈ Q ∥ P

    comp-end : P ∥ 𝟘 ≈ P

    scope-end : _≈_ {n} (ν 𝟘 ⦃ name ⦄) 𝟘

    scope-ext : (u : Unused zero P)
              → ν (P ∥ Q) ⦃ name ⦄ ≈ lower zero P u ∥ (ν Q) ⦃ name ⦄

    scope-scope-comm : ν (ν P ⦃ namey ⦄) ⦃ namex ⦄ ≈ ν (ν (exchange zero P) ⦃ namex ⦄) ⦃ namey ⦄

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
    ν-cong_      : P ≅⟨ r ⟩ P' → ν P ⦃ name ⦄      ≅⟨ one r ⟩ ν P' ⦃ name ⦄
    comp-cong_   : P ≅⟨ r ⟩ P' → P ∥ Q             ≅⟨ one r ⟩ P' ∥ Q
    input-cong_  : P ≅⟨ r ⟩ P' → (x ⦅⦆ P) ⦃ name ⦄ ≅⟨ one r ⟩ (x ⦅⦆ P') ⦃ name ⦄
    output-cong_ : P ≅⟨ r ⟩ P' → x ⟨ y ⟩ P         ≅⟨ one r ⟩ x ⟨ y ⟩ P'

  _≅_ : Scoped n → Scoped n → Set
  P ≅ Q = ∃[ r ] (P ≅⟨ r ⟩ Q)

  _[_↦_]' : Fin n → Fin n → Fin n → Fin n
  x [ i ↦ j ]' with i Finₚ.≟ x
  x [ i ↦ j ]' | true because _ = j
  x [ i ↦ j ]' | false because _ = x

  _[_↦_] : Scoped n → (i j : Fin n) → Scoped n
  𝟘           [ i ↦ j ] = 𝟘
  (ν P)       [ i ↦ j ] = ν (P [ suc i ↦ suc j ])
  (P ∥ Q)     [ i ↦ j ] = (P [ i ↦ j ]) ∥ (Q [ i ↦ j ])
  (x ⦅⦆ P)    [ i ↦ j ] = (x [ i ↦ j ]') ⦅⦆ (P [ suc i ↦ suc j ])
  (x ⟨ y ⟩ P) [ i ↦ j ] = (x [ i ↦ j ]') ⟨ y [ i ↦ j ]' ⟩ (P [ i ↦ j ])

  substFin-unused : ∀ {i j} (x : Fin (suc n)) → i ≢ j → i ≢ x [ i ↦ j ]'
  substFin-unused {i = i} x i≢j  with i Finₚ.≟ x
  substFin-unused {i = i} x i≢j | true because _ = i≢j
  substFin-unused {i = i} x i≢j | false because ofⁿ ¬p = ¬p

  subst-unused : {i j : Fin (suc n)}
               → i ≢ j
               → (P : Scoped (suc n))
               → Unused i (P [ i ↦ j ])
  subst-unused i≢j 𝟘 = tt
  subst-unused i≢j (ν P) = subst-unused (λ i≡j → i≢j (Finₚ.suc-injective i≡j)) P
  subst-unused i≢j (P ∥ Q) = subst-unused i≢j P , subst-unused i≢j Q
  subst-unused i≢j (x ⦅⦆ P) = substFin-unused x i≢j , subst-unused (λ i≡j → i≢j (Finₚ.suc-injective i≡j)) P
  subst-unused i≢j (x ⟨ y ⟩ P) = substFin-unused x i≢j , substFin-unused y i≢j , subst-unused i≢j P

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

    comm : {P : Scoped (1 + n)} {Q : Scoped n} {i j : Fin n}
         → let uP' = subst-unused (λ ()) P
         in ((i ⦅⦆ P) ⦃ name ⦄) ∥ (i ⟨ j ⟩ Q) =[ external i ]⇒ lower zero (P [ zero ↦ suc j ]) uP' ∥ Q

    par_ : ∀ {c} {P P' Q : Scoped n}
         → P =[ c ]⇒ P'
         → P ∥ Q =[ c ]⇒ P' ∥ Q

    res_ : ∀ {c} {P Q : Scoped (1 + n)}
         → P =[ c ]⇒ Q
         → ν P ⦃ name ⦄ =[ dec c ]⇒ ν Q ⦃ name ⦄

    struct : ∀ {c} {P P' Q' Q : Scoped n}
           → P ≅⟨ r ⟩ P'
           → P' =[ c ]⇒ Q'
           → Q' ≅⟨ r ⟩ Q
           → P =[ c ]⇒ Q

  _⇒_ : Scoped n → Scoped n → Set
  P ⇒ Q = ∃[ c ] (P =[ c ]⇒ Q)
