{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst; inspect; [_])
open import Relation.Nullary using (_because_; ofʸ; ofⁿ)
open import Function using (id)

open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Bool.Base using (false; true)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Fin as Fin using (Fin ; zero ; suc; #_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Unary.All as All using (All)

import Data.Vec.Relation.Unary.All.Properties as Allₚ
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ


open import PiCalculus.Syntax
open Scoped

import PiCalculus.Utils
open PiCalculus.Utils.All2Vec
open PiCalculus.Utils.Sum

module PiCalculus.Semantics where

  private
    variable
      n m l : ℕ
      nx ny : Name
      ns : Vec Name n
      P P' Q R : Scoped n
      x y : Fin n
      ys : Vec (Fin n) m

  data _+_≔_ : ℕ → ℕ → ℕ → Set where
    zero  :             zero  + zero  ≔ zero
    left  : n + m ≔ l → suc n + m     ≔ suc l
    right : n + m ≔ l → n     + suc m ≔ suc l

  invert : n + m ≔ l → Fin l → Fin n ⊎ Fin m
  invert (left ρ) zero = inj₁ zero
  invert (right ρ) zero = inj₂ zero
  invert (left ρ) (suc x) = Sum.map suc id (invert ρ x)
  invert (right ρ) (suc x) = Sum.map id suc (invert ρ x)

  +-identityʳ : n + zero ≔ n
  +-identityʳ {zero} = zero
  +-identityʳ {suc n} = left +-identityʳ

  +-comm : n + m ≔ l → m + n ≔ l
  +-comm zero = zero
  +-comm (left ρ) = right (+-comm ρ)
  +-comm (right ρ) = left (+-comm ρ)

  right-first : ∀ n m → n + m ≔ (m ℕ.+ n)
  right-first zero zero = zero
  right-first (suc n) zero = left (right-first n zero)
  right-first n (suc m) = right (right-first n m)

  extend : ∀ k → n + m ≔ l → (k ℕ.+ n) + m ≔ (k ℕ.+ l)
  extend {n = n} {l = l} zero ρ = ρ
  extend {n = n} {l = l} (suc k) ρ = left (extend k ρ)

  IsLeftFin : n + m ≔ l → Fin l → Set
  IsLeftFin ρ x = IsInj₁ (invert ρ x)

  IsLeft : n + m ≔ l → Scoped l → Set
  IsLeft ρ 𝟘 = ⊤
  IsLeft ρ (ν P) = IsLeft (left ρ) P
  IsLeft ρ (P ∥ Q) = IsLeft ρ P × IsLeft ρ Q
  IsLeft ρ (x ⦅ m ⦆ P) = IsLeftFin ρ x × IsLeft (extend m ρ) P
  IsLeft ρ (x ⟨ ys ⟩ P) = IsLeftFin ρ x × All (IsLeftFin ρ) ys × IsLeft ρ P

  ----------------------------------------------------------
  -- Punch Out (lowering, stregthening)

  punchOutFin : (ρ : n + m ≔ l) (x : Fin l) → IsLeftFin ρ x → Fin n
  punchOutFin ρ x il with invert ρ x
  punchOutFin ρ x il | inj₁ l = l

  punchOut : (ρ : n + m ≔ l) (P : Scoped l) → IsLeft ρ P → Scoped n
  punchOut ρ 𝟘 il = 𝟘
  punchOut ρ (ν P) il = ν (punchOut (left ρ) P il)
  punchOut ρ (P ∥ Q) (ilP , ilQ) = punchOut ρ P ilP ∥ punchOut ρ Q ilQ
  punchOut ρ (x ⦅ m ⦆ P) (ilx , ilP) = punchOutFin ρ x ilx ⦅ m ⦆ punchOut (extend m ρ) P ilP
  punchOut ρ (x ⟨ ys ⟩ P) (ilx , ilys , ilP) =
    punchOutFin ρ x ilx ⟨ all2vec (punchOutFin ρ _) ilys ⟩ punchOut ρ P ilP

  ----------------------------------------------------------
  -- Punch In (lifting, weakening)

  punchInFin : n + m ≔ l → Fin n → Fin l
  punchInFin (left ρ) zero = zero
  punchInFin (left ρ) (suc x) = suc (punchInFin ρ x)
  punchInFin (right ρ) x = suc (punchInFin ρ x)

  punchIn : n + m ≔ l → Scoped n → Scoped l
  punchIn ρ 𝟘 = 𝟘
  punchIn ρ (ν P) = ν (punchIn (left ρ) P)
  punchIn ρ (P ∥ Q) = punchIn ρ P ∥ punchIn ρ Q
  punchIn ρ (x ⦅ m ⦆ P) = punchInFin ρ x ⦅ m ⦆ punchIn (extend m ρ) P
  punchIn ρ (x ⟨ ys ⟩ P) = punchInFin ρ x ⟨ map (punchInFin ρ) ys ⟩ punchIn ρ P

  left-IsLeftFin : (ρ : n + m ≔ l) → IsLeftFin ρ x → IsLeftFin (left ρ) (suc x)
  left-IsLeftFin {x = x} ρ il with invert ρ x
  left-IsLeftFin {x = x} ρ il | inj₁ _ = tt

  right-IsLeftFin : (ρ : n + m ≔ l) → IsLeftFin ρ x → IsLeftFin (right ρ) (suc x)
  right-IsLeftFin {x = x} ρ il with invert ρ x
  right-IsLeftFin {x = x} ρ il | inj₁ _ = tt

  punchInFin-IsLeftFin : (ρ : n + m ≔ l) (x : Fin n) → IsLeftFin ρ (punchInFin ρ x)
  punchInFin-IsLeftFin (left ρ) zero = tt
  punchInFin-IsLeftFin (left ρ) (suc x) = left-IsLeftFin ρ (punchInFin-IsLeftFin ρ x)
  punchInFin-IsLeftFin (right ρ) x = right-IsLeftFin ρ (punchInFin-IsLeftFin ρ x)

  ----------------------------------------------------------
  -- Exchange

  exchangeFin : m + 2 ≔ l → Fin l → Fin l
  exchangeFin ρ x with invert ρ x
  exchangeFin ρ x | inj₁ r = x
  exchangeFin ρ x | inj₂ zero = punchInFin (+-comm ρ) (suc zero)
  exchangeFin ρ x | inj₂ (suc zero) = punchInFin (+-comm ρ) zero

  exchange : n + 2 ≔ l → Scoped l → Scoped l
  exchange ρ 𝟘 = 𝟘
  exchange ρ (ν P) = ν (exchange (left ρ) P)
  exchange ρ (P ∥ Q) = exchange ρ P ∥ exchange ρ Q
  exchange ρ (x ⦅ m ⦆ P) = exchangeFin ρ x ⦅ m ⦆ exchange (extend m ρ) P
  exchange ρ (x ⟨ ys ⟩ P) = exchangeFin ρ x ⟨ map (exchangeFin ρ) ys ⟩ exchange ρ P

  ----------------------------------------------------------
  -- Simultaneous renaming

  _[_↦_]-Fin : Fin l → n + m ≔ l → Vec (Fin n) m → Fin l
  x [ ρ ↦ xs ]-Fin with invert ρ x
  (x [ ρ ↦ xs ]-Fin) | inj₁ l = x
  (x [ ρ ↦ xs ]-Fin) | inj₂ r = punchInFin ρ (Vec.lookup xs r)

  _[_↦_] : Scoped l → n + m ≔ l → Vec (Fin n) m → Scoped l
  𝟘 [ ρ ↦ xs ] = 𝟘
  ν P [ ρ ↦ xs ] = ν (P [ left ρ ↦ map suc xs ])
  (P ∥ Q) [ ρ ↦ xs ] = (P [ ρ ↦ xs ]) ∥ (Q [ ρ ↦ xs ])
  (x ⦅ m ⦆ P) [ ρ ↦ xs ] = (x [ ρ ↦ xs ]-Fin) ⦅ m ⦆ (P [ extend m ρ ↦ map (Fin.raise m) xs ])
  (x ⟨ ys ⟩ P) [ ρ ↦ xs ] = (x [ ρ ↦ xs ]-Fin) ⟨ map (_[ ρ ↦ xs ]-Fin) ys ⟩ (P [ ρ ↦ xs ])

  subst-IsLeftFin : {xs : Vec (Fin n) m} (ρ : n + m ≔ l) (x : Fin l)
                  → IsLeftFin ρ (x [ ρ ↦ xs ]-Fin)
  subst-IsLeftFin {xs = xs} ρ x with invert ρ x | inspect (invert ρ) x
  subst-IsLeftFin {xs = xs} ρ x | inj₁ _ | [ eq ] rewrite eq = tt
  subst-IsLeftFin {xs = xs} ρ x | inj₂ q | eq = punchInFin-IsLeftFin ρ (Vec.lookup xs q)

  subst-IsLeft : {xs : Vec (Fin n) m} (ρ : n + m ≔ l) (P : Scoped l) → IsLeft ρ (P [ ρ ↦ xs ])
  subst-IsLeft ρ 𝟘 = tt
  subst-IsLeft ρ (ν P) = subst-IsLeft (left ρ) P
  subst-IsLeft ρ (P ∥ Q) = (subst-IsLeft ρ P) , (subst-IsLeft ρ Q)
  subst-IsLeft ρ (x ⦅ m ⦆ P) = subst-IsLeftFin ρ x , subst-IsLeft (extend m ρ) P
  subst-IsLeft ρ (x ⟨ ys ⟩ P) = subst-IsLeftFin ρ x , Allₚ.map⁺ (All.universal (subst-IsLeftFin ρ ) ys) , subst-IsLeft ρ P

  ----------------------------------------------------------
  -- Structural Congruence

  infixl 10 _≈_
  data _≈_ : Scoped n → Scoped n → Set where
    comp-assoc : P ∥ (Q ∥ R) ≈ (P ∥ Q) ∥ R

    comp-symm : P ∥ Q ≈ Q ∥ P

    comp-end : P ∥ 𝟘 ≈ P

    scope-end : _≈_ {n} (ν 𝟘 ⦃ nx ⦄) 𝟘

    scope-ext : (il : IsLeft (right +-identityʳ) P)
              → ν (P ∥ Q) ⦃ nx ⦄ ≈ punchOut (right +-identityʳ) P il ∥ (ν Q) ⦃ nx ⦄

    scope-scope-comm : ν (ν P ⦃ ny ⦄) ⦃ nx ⦄ ≈ ν (ν (exchange (right (right +-identityʳ)) P) ⦃ nx ⦄) ⦃ ny ⦄

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
    ν-cong_      : P ≅⟨ r ⟩ P' → ν P ⦃ nx ⦄      ≅⟨ one r ⟩ ν P' ⦃ nx ⦄
    comp-cong_   : P ≅⟨ r ⟩ P' → P ∥ Q             ≅⟨ one r ⟩ P' ∥ Q
    input-cong_  : P ≅⟨ r ⟩ P' → (x ⦅ n ⦆ P) ⦃ ns ⦄ ≅⟨ one r ⟩ (x ⦅ n ⦆ P') ⦃ ns ⦄
    output-cong_ : P ≅⟨ r ⟩ P' → x ⟨ ys ⟩ P         ≅⟨ one r ⟩ x ⟨ ys ⟩ P'

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

  ----------------------------------------------------------
  -- Reduction

  infixl 5 _=[_]⇒_
  data _=[_]⇒_ : Scoped n → Channel n → Scoped n → Set where

    comm : {P : Scoped (m ℕ.+ n)} {Q : Scoped n} {x : Fin n} {ys : Vec (Fin n) m} →
         let
           m+n = right-first n m
           gr = subst-IsLeft m+n P
           P' = punchOut m+n (P [ m+n ↦ ys ]) gr
         in
         (x ⦅ m ⦆ P) ⦃ ns ⦄ ∥ (x ⟨ ys ⟩ Q)
           =[ external x ]⇒
         P' ∥ Q

    par_ : ∀ {c} {P P' Q : Scoped n}
         → P =[ c ]⇒ P'
         → P ∥ Q =[ c ]⇒ P' ∥ Q

    res_ : ∀ {c} {P Q : Scoped (1 ℕ.+ n)}
         → P =[ c ]⇒ Q
         → ν P ⦃ nx ⦄ =[ dec c ]⇒ ν Q ⦃ nx ⦄

    struct : ∀ {c} {P Q P' : Scoped n}
           → P ≅⟨ r ⟩ P'
           → P' =[ c ]⇒ Q
           → P =[ c ]⇒ Q

  _⇒_ : Scoped n → Scoped n → Set
  P ⇒ Q = ∃[ c ] (P =[ c ]⇒ Q)
