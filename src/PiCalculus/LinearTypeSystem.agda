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
open import PiCalculus.Quantifiers

module PiCalculus.LinearTypeSystem (Ω : Quantifiers) where
open Quantifiers Ω

infix 50 _↑_↓
infixr 4 _w_⊢_⊠_
infixr 4 _w_∋_w_⊠_
infixr 10 base chan recv send

private
  variable
    i i' : I
    n : ℕ

data Type : Set
shape : Type → ℕ
Usage : I × Type → Set

Usage (i , t) = Vec (Cs i) (shape t)

data Type where
  B[_]   : ℕ → Type
  C[_w_] : (t : Type) → Usage (i , t) → Type
  P[_&_] : Type → Type → Type

shape B[ _ ] = 0
shape C[ _ w _ ] = 2
shape P[ _ & _ ] = 0

PreCtx : ℕ → Set
PreCtx = Vec (I × Type)

Ctx : ∀ {n} → PreCtx n → Set
Ctx = All Usage

private
  variable
    γ : PreCtx n
    Γ Δ Ξ Θ : Ctx γ
    b : ℕ
    t t' : Type
    xs ys zs : Usage (i , t)
    P Q : Scoped n

ε : {γ : PreCtx n} → Ctx γ
ε {γ = []} = []
ε {γ = _ -, _} = ε -, Vec.replicate 0∙

data _w_∋_w_⊠_ : (γ : PreCtx n) → Ctx γ
               → (t : Type) → Usage (i , t)
               → Ctx γ → Set where

  zero : {Γ : Ctx γ} {ys zs : Usage (i , t)}
       → {check : True (∙ᵥ-compute ys zs)}
       → γ -, (i , t) w Γ -, proj₁ (toWitness check) ∋ t w ys ⊠ Γ -, zs

  suc : {Γ Δ : Ctx γ} {xs : Usage (i , t)} {xs' : Usage (i' , t')}
      → γ w Γ ∋ t w xs ⊠ Δ
      → γ -, (i' , t') w Γ -, xs' ∋ t w xs ⊠ Δ -, xs'

toFin : {γ : PreCtx n} {Γ Δ : Ctx γ} {xs : Usage (i , t)}
      → γ w Γ ∋ t w xs ⊠ Δ
      → Fin n
toFin zero = zero
toFin (suc x) = suc (toFin x)

_↑_↓ : Cs i → Cs i → Vec (Cs i) 2
μ↑ ↑ μ↓ ↓ = μ↓ ∷ μ↑ ∷ []

data _w_⊢_⊠_ : (γ : PreCtx n) → Ctx γ → Scoped n → Ctx γ → Set where

  end : γ w Γ ⊢ 𝟘 ⊠ Γ

  base : γ -, (∃I , B[ b ]) w Γ -, [] ⊢ P     ⊠ Δ -, []
       ------------------------------------------------
       → γ                  w Γ       ⊢ +[] P ⊠ Δ

  chan : (t : Type) (m : Usage (i' , t)) (μ : Cs i)
       → γ -, (_ , C[ t w m ]) w Γ -, μ ↑ μ ↓ ⊢ P     ⊠ Δ -, 0∙ ↑ 0∙ ↓
       ---------------------------------------------------------------
       → γ                     w Γ            ⊢ new P ⊠ Δ

  recv : {t : Type} {m : Usage (i' , t)}
       → (x : γ            w Γ       ∋ C[ t w m ] w 0∙ {i} ↑ 1∙ ↓ ⊠ Ξ)
       →      γ -, (_ , t) w Ξ -, m  ⊢ P                          ⊠ Θ -, Vec.replicate 0∙
       ----------------------------------------------------------------------------------
       →      γ            w Γ       ⊢ toFin x ⦅⦆ P               ⊠ Θ

  send : {t : Type} {m : Usage (i' , t)}
       → (x : γ w Γ ∋ C[ t w m ] w 1∙ {i} ↑ 0∙ ↓ ⊠ Δ)
       → (y : γ w Δ ∋ t          w m             ⊠ Ξ)
       →      γ w Ξ ⊢ P                          ⊠ Θ
       ---------------------------------------------
       →      γ w Γ ⊢ toFin x ⟨ toFin y ⟩ P      ⊠ Θ

  comp : γ w Γ ⊢ P     ⊠ Δ
       → γ w Δ ⊢ Q     ⊠ Ξ
       -------------------
       → γ w Γ ⊢ P ∥ Q ⊠ Ξ

_w_⊢_ : (γ : PreCtx n) → Ctx γ → Scoped n → Set
γ w Γ ⊢ P = γ w Γ ⊢ P ⊠ ε
