{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong)
open import Relation.Nullary using (_because_; ofʸ; ofⁿ)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
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
      n m : ℕ
      P P' Q R : Scoped n
      x y : Fin n

  -- A renaming (thin x) pushes up everithing x and above
  thin : Fin (suc n) → Fin n → Fin (suc n)
  thin zero y = suc y
  thin (suc x) zero = zero
  thin (suc x) (suc y) = suc (thin x y)

  -- A renaming (thick x) tries to lower everything above x
  -- Only succeeds if x itself is not present
  thick : Fin (suc n) → Fin (suc n) → Maybe (Fin n)
  thick zero zero = nothing
  thick zero (suc y) = just y
  thick {suc n} (suc x) zero = just zero
  thick {suc n} (suc x) (suc y) = Maybe.map suc (thick x y)

  exchangeFin : Fin n → Fin (suc n) → Fin (suc n)
  exchangeFin zero zero = suc zero
  exchangeFin zero (suc zero) = zero
  exchangeFin zero (suc (suc x)) = suc (suc x)
  exchangeFin (suc i) zero = zero
  exchangeFin (suc i) (suc x) = suc (exchangeFin i x)

  _for_ : Fin n → Fin (suc n) → Fin (suc n) → Fin n
  (x' for x) y = Maybe.fromMaybe x' (thick x y)

  suc-|> : (Fin n → Fin m) → (Fin (suc n) → Fin (suc m))
  suc-|> f zero = zero
  suc-|> f (suc x) = suc (f x)

  |> : (Fin n → Fin m) → Scoped n → Scoped m
  |> f 𝟘 = 𝟘
  |> f (ν P) = ν (|> (suc-|> f) P)
  |> f (P ∥ Q) = |> f P ∥ |> f Q
  |> f (x ⦅⦆ P) = f x ⦅⦆ |> (suc-|> f) P
  |> f (x ⟨ y ⟩ P) = f x ⟨ f y ⟩ |> f P

  Unused : Fin n → Scoped n → Set
  Unused i 𝟘 = ⊤
  Unused i (ν P) = Unused (suc i) P
  Unused i (P ∥ Q) = Unused i P × Unused i Q
  Unused i (x ⦅⦆ P) = i ≢ x × Unused (suc i) P
  Unused i (x ⟨ y ⟩ P) = i ≢ x × i ≢ y × Unused i P

  lower : (i : Fin (suc n)) (P : Scoped (suc n)) → Unused i P → Scoped n
  lower {n = zero} zero 𝟘 UiP = 𝟘
  lower {n = zero} zero (ν P) UiP = ν (lower (suc zero) P UiP)
  lower {n = zero} zero (P ∥ Q) (UiP , UiQ) = lower zero P UiP ∥ lower zero Q UiQ
  lower {n = zero} zero (zero ⦅⦆ P) (i≢x , UiP) = contradiction refl i≢x
  lower {n = zero} zero (zero ⟨ y ⟩ P) (i≢x , i≢y , UiP) = contradiction refl i≢x
  lower {n = suc n} i P UiP = |> (zero for i) P

  infixl 10 _≈_
  data _≈_ : Scoped n → Scoped n → Set where
    comp-assoc : P ∥ (Q ∥ R) ≈ (P ∥ Q) ∥ R

    comp-symm : P ∥ Q ≈ Q ∥ P

    comp-end : P ∥ 𝟘 ≈ P

    scope-end : _≈_ {n} (ν 𝟘 ⦃ name ⦄) 𝟘

    scope-ext : (u : Unused zero P)
              → ν (P ∥ Q) ⦃ name ⦄ ≈ lower zero P u ∥ (ν Q) ⦃ name ⦄

    scope-scope-comm : ν (ν P ⦃ namey ⦄) ⦃ namex ⦄ ≈ ν (ν (|> (exchangeFin zero) P) ⦃ namex ⦄) ⦃ namey ⦄

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
         → ((i ⦅⦆ P) ⦃ name ⦄) ∥ (i ⟨ j ⟩ Q)
             =[ external i ]⇒
           |> (j for zero) P ∥ Q

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
