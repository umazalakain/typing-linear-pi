{-# OPTIONS --safe --without-K #-}

open import Relation.Nullary.Decidable using (True; toWitness)
open import Function using (_∘_)

import Data.Product as Product
import Data.Unit as Unit
import Data.Fin as Fin
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All

open Product using (Σ; Σ-syntax; _×_; _,_; proj₁)
open Unit using (⊤; tt)
open Nat using (ℕ; zero; suc)
open Fin using (Fin; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)

open import PiCalculus.Syntax
open Scoped
open import PiCalculus.LinearTypeSystem.Algebras

module PiCalculus.LinearTypeSystem (Ω : Algebras) where
open Algebras Ω

infixr 4 _；_⊢_▹_
infixr 4 _；_∋[_]_；_▹_ _∋[_]_▹_ _∋[_]_
infixr 10 ν _⦅⦆_ _⟨_⟩_

private
  variable
    name : Name
    idx idx' : Idx
    n : ℕ
    i j : Fin n

data Type : Set where
  𝟙      : Type
  B[_]   : ℕ → Type
  C[_；_] : Type → (Usage idx) ² → Type
  -- P[_&_] : Type → Type → Type

-- Context of types
PreCtx : ℕ → Set
PreCtx = Vec Type

-- Context of usage indices
Idxs : ℕ → Set
Idxs = Vec Idx

-- Indexed context of usages
Ctx : ∀ {n} → Idxs n → Set
Ctx = All λ idx → (Usage idx) ²

private
  variable
    γ : PreCtx n
    idxs : Idxs n
    Γ Δ Ξ Θ : Ctx idxs
    b : ℕ
    t t' : Type
    x y z : Usage idx
    P Q : Scoped n

-- γ ∋[ i ] t is a proof that variable i in Γ has type t
data _∋[_]_ : PreCtx n → Fin n → Type → Set where
  zero : γ -, t ∋[ zero ] t
  suc : γ ∋[ i ] t → γ -,  t' ∋[ suc i ] t

-- Γ ∋[ i ] x ▹ Δ is a proof that subtracting x from variable in in Γ results in Δ
data _∋[_]_▹_ : {idxs : Idxs n} → Ctx idxs → Fin n → (Usage idx) ² → Ctx idxs → Set where

  zero : {idxs : Idxs n} {Γ : Ctx idxs} {x y z : Usage idx ²}
       → x ≔ y ∙² z
       → Γ -, x ∋[ zero {n} ] y ▹ Γ -, z

  suc : {Γ Δ : Ctx idxs} {x : (Usage idx) ² } {x' : (Usage idx') ²}
      → Γ ∋[ i ] x ▹ Δ
      → Γ -, x' ∋[ suc i ] x ▹ Δ -, x'

-- For convenience, merge together γ ∋[ i ] t and Γ ∋[ i ] x ▹ Δ
_；_∋[_]_；_▹_ : {idxs : Idxs n} → PreCtx n → Ctx idxs → Fin n → Type → (Usage idx) ² → Ctx idxs → Set
γ ； Γ ∋[ i ] t ； x ▹ Δ = (γ ∋[ i ] t) × (Γ ∋[ i ] x ▹ Δ)

-- Constructor for (zero , zero xyz) that computes z from x and y
here : {γ : PreCtx n} {idxs : Idxs n} {Γ : Ctx idxs} {x y : Usage idx ²} ⦃ check : True (∙²-computeʳ x y) ⦄
     → γ -, t ； Γ -, x ∋[ zero ] t ； y ▹ Γ -, proj₁ (toWitness check)
here ⦃ check ⦄ = let _ , x≔y∙²z = toWitness check in zero , zero x≔y∙²z

infixr 20 there_
there_ : {γ : PreCtx n} {idxs : Idxs n} {Γ Δ : Ctx idxs} {x : Usage idx ²} {x' : Usage idx' ²}
       → γ       ； Γ       ∋[     i ] t ； x ▹ Δ
       → γ -, t' ； Γ -, x' ∋[ suc i ] t ； x ▹ Δ -, x'
there_ (i , j) = suc i , suc j

-- Typing judgment γ ； Γ ⊢ P ▹ Δ where P is a well-typed process
-- under typing context γ and input and output usage contexts Γ and Δ
data _；_⊢_▹_ : {idxs : Idxs n} → PreCtx n → Ctx idxs → Scoped n → Ctx idxs → Set where

  𝟘 : γ ； Γ ⊢ 𝟘 ▹ Γ

  -- Note (μ , μ): the created channel is balanced
  ν : ∀ (t : Type) {idx' : Idx} (m : Usage idx' ²) {idx : Idx} (μ : Usage idx)
    → γ -, C[ t ； m ] ； Γ -, (μ , μ) ⊢ P            ▹ Δ -, ℓ∅
    -----------------------------------------------------
    → γ               ； Γ             ⊢ ν P ⦃ name ⦄ ▹ Δ

  _⦅⦆_ : ∀ {t : Type} {m : (Usage idx') ²}
       → γ      ； Γ       ∋[ i ] C[ t ； m ] ； ℓᵢ {idx} ▹ Ξ
       → γ -, t ； Ξ -, m  ⊢      P                      ▹ Θ -, ℓ∅
       -----------------------------------------------------------
       → γ      ； Γ       ⊢ (i ⦅⦆ P) ⦃ name ⦄           ▹ Θ

  _⟨_⟩_ : {t : Type} {m : (Usage idx') ²}
        → γ ； Γ ∋[ i ] C[ t ； m ] ； ℓₒ {idx} ▹ Δ
        → γ ； Δ ∋[ j ] t           ； m        ▹ Ξ
        → γ ； Ξ ⊢      P                       ▹ Θ
        -----------------------------------------
        → γ ； Γ ⊢      i ⟨ j ⟩ P               ▹ Θ

  _∥_ : γ ； Γ ⊢ P     ▹ Δ
      → γ ； Δ ⊢ Q     ▹ Ξ
      -------------------
      → γ ； Γ ⊢ P ∥ Q ▹ Ξ

_；[_]_⊢_▹_ : PreCtx n → (idxs : Idxs n) → Ctx idxs → Scoped n → Ctx idxs → Set
γ ；[ idxs ] Γ ⊢ P ▹ Δ = _；_⊢_▹_ {idxs = idxs} γ Γ P Δ
