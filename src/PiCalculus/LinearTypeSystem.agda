open import Relation.Nullary.Decidable using (True; toWitness)
open import Function using (_∘_)

import Data.Product as Product
import Data.Unit as Unit
import Data.Fin as Fin
import Data.Nat as Nat
import Data.Bool as Bool
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
infixr 4 _∝_∋_∝_⊠_
infixr 10 chan recv send

private
  variable
    i i' : I
    n : ℕ

data Type : Set where
  B[_]   : ℕ → Type
  C[_∝_] : Type → Cs i → Type
  P[_&_] : Type → Type → Type

PreCtx : ℕ → Set
PreCtx = Vec Type

Ctx : ∀ {n} → Vec I n → Set
Ctx = All Cs

private
  variable
    γ : PreCtx n
    is : Vec I n
    Γ Δ Ξ Θ : Ctx is
    b : ℕ
    t t' : Type
    x y z : Cs i
    P Q : Scoped n

data _∝_∋_∝_⊠_ : PreCtx n → Ctx is
               → Type → Cs i
               → Ctx is → Set where

  zero : {Γ : Ctx is} {y z : Cs i}
       → {check : True (∙-compute y z)}
       → γ -, t ∝ Γ -, proj₁ (toWitness check) ∋ t ∝ y ⊠ Γ -, z

  suc : {Γ Δ : Ctx is} {x : Cs i} {x' : Cs i'}
      → γ ∝ Γ ∋ t ∝ x ⊠ Δ
      → γ -,  t' ∝ Γ -, x' ∋ t ∝ x ⊠ Δ -, x'

toFin : {γ : PreCtx n} {Γ Δ : Ctx is} {x : Cs i}
      → γ ∝ Γ ∋ t ∝ x ⊠ Δ
      → Fin n
toFin zero = zero
toFin (suc x) = suc (toFin x)

data _∝_⊢_⊠_ : PreCtx n → Ctx is → Scoped n → Ctx is → Set where

  end : γ ∝ Γ ⊢ 𝟘 ⊠ Γ

  chan : (t : Type) (m : Cs i') (μ : Cs i)
       → γ -, C[ t ∝ m ] ∝ Γ -, μ ⊢ P     ⊠ Δ -, 0∙
       --------------------------------------------
       → γ               ∝ Γ      ⊢ new P ⊠ Δ

  recv : {t : Type} {m : Cs i'}
       → (x : γ      ∝ Γ       ∋ C[ t ∝ m ] ∝ +∙ {i} ⊠ Ξ)
       →      γ -, t ∝ Ξ -, m  ⊢ P                   ⊠ Θ -, 0∙
       -------------------------------------------------------
       →      γ      ∝ Γ       ⊢ toFin x ⦅⦆ P        ⊠ Θ

  send : {t : Type} {m : Cs i'}
       → (x : γ ∝ Γ ∋ C[ t ∝ m ] ∝ -∙ {i}   ⊠ Δ)
       → (y : γ ∝ Δ ∋ t          ∝ m        ⊠ Ξ)
       →      γ ∝ Ξ ⊢ P                     ⊠ Θ
       -----------------------------------------
       →      γ ∝ Γ ⊢ toFin x ⟨ toFin y ⟩ P ⊠ Θ

  comp : γ ∝ Γ ⊢ P     ⊠ Δ
       → γ ∝ Δ ⊢ Q     ⊠ Ξ
       -------------------
       → γ ∝ Γ ⊢ P ∥ Q ⊠ Ξ

_∝_⊢_ : PreCtx n → Ctx is → Scoped n → Set
γ ∝ Γ ⊢ P = γ ∝ Γ ⊢ P ⊠ ε
