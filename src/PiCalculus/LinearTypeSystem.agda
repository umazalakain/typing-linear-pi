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
open Syntax
open Scoped
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem (Ω : Quantifiers) where
open Quantifiers Ω

infixr 4 _∝_⊢_⊠_
infixr 4 _∝_[_]≔_∝_⊠_
infixr 10 chan recv send

private
  variable
    idx idx' : Idx
    n : ℕ
    i j : Fin n

data Type : Set where
  𝟙      : Type
  B[_]   : ℕ → Type
  C[_∝_] : Type → (Carrier idx) ² → Type
  -- P[_&_] : Type → Type → Type

PreCtx : ℕ → Set
PreCtx = Vec Type

private
  variable
    γ : PreCtx n
    idxs : Idxs n
    Γ Δ Ξ Θ : Ctx idxs
    b : ℕ
    t t' : Type
    x y z : Carrier idx
    P Q : Scoped n

data _∝_[_]≔_∝_⊠_ : PreCtx n → Ctx idxs → Fin n → Type → (Carrier idx) ² → Ctx idxs → Set where

  zero : {Γ : Ctx idxs} {y z : (Carrier idx) ²}
       → ⦃ check : True (∙²-compute y z) ⦄
       → γ -, t ∝ Γ -, proj₁ (toWitness check) [ zero ]≔ t ∝ y ⊠ Γ -, z

  suc : {Γ Δ : Ctx idxs} {x : (Carrier idx) ² } {x' : (Carrier idx') ²}
      → γ ∝ Γ [ i ]≔ t ∝ x ⊠ Δ
      → γ -,  t' ∝ Γ -, x' [ suc i ]≔ t ∝ x ⊠ Δ -, x'


data _∝_⊢_⊠_ : PreCtx n → Ctx idxs → Scoped n → Ctx idxs → Set where

  end : γ ∝ Γ ⊢ 𝟘 ⊠ Γ

  chan : (t : Type) (m : (Carrier idx') ²) (μ : Carrier idx)
       → γ -, C[ t ∝ m ] ∝ Γ -, (μ , μ) ⊢ P     ⊠ Δ -, ℓ∅
       -----------------------------------------------------
       → γ               ∝ Γ            ⊢ new P ⊠ Δ

  recv : {t : Type} {m : (Carrier idx') ²}
       → (x : γ      ∝ Γ       [ i ]≔ C[ t ∝ m ] ∝ ℓᵢ {idx} ⊠ Ξ)
       →      γ -, t ∝ Ξ -, m  ⊢      P                     ⊠ Θ -, ℓ∅
       --------------------------------------------------------------
       →      γ      ∝ Γ       ⊢ i ⦅⦆ P        ⊠ Θ

  send : {t : Type} {m : (Carrier idx') ²}
       → (x : γ ∝ Γ [ i ]≔ C[ t ∝ m ] ∝ ℓₒ {idx} ⊠ Δ)
       → (y : γ ∝ Δ [ j ]≔ t          ∝ m        ⊠ Ξ)
       →      γ ∝ Ξ ⊢      P                     ⊠ Θ
       -------------------------------------------
       →      γ ∝ Γ ⊢ i ⟨ j ⟩ P ⊠ Θ

  comp : γ ∝ Γ ⊢ P     ⊠ Δ
       → γ ∝ Δ ⊢ Q     ⊠ Ξ
       -------------------
       → γ ∝ Γ ⊢ P ∥ Q ⊠ Ξ

_∝_⊢_ : PreCtx n → Ctx idxs → Scoped n → Set
γ ∝ Γ ⊢ P = γ ∝ Γ ⊢ P ⊠ ε
