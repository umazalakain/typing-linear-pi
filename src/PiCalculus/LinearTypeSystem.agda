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

infixr 4 _∋[_]_▹_
infixr 10 ν _⦅⦆_ _⟨_⟩_

private
  variable
    idx idx' : Idx
    n : ℕ
    i j : Fin n

data Type : Set₁ where
  Pure : Set → Type
  Chan : (idx : Idx) → Usage idx → Usage idx → Type → Type
  Pair : Type → Type → Type

Ctx : ℕ → Set₁
Ctx = Vec Type

variable
  s t r : Type
  Γ Δ Θ Ξ : Ctx n
  P Q : Scoped n

data TypeSplit : Type → Type → Type → Set₁ where
  pure  : ∀ {A}
        → TypeSplit (Pure A)   (Pure A)   (Pure A)
  pair  : ∀ {l ll lr r rl rr}
        → TypeSplit l ll lr
        → TypeSplit r rl rr
        → TypeSplit (Pair l r) (Pair ll rl) (Pair lr rr)
  chan  : ∀ {t i o il ol ir or}
        → i ≔ il ∙ ir
        → o ≔ ol ∙ or
        → TypeSplit (Chan idx i o t) (Chan idx il ol t) (Chan idx ir or t)

data _∋[_]_▹_ : Ctx n → Fin n → Type → Ctx n → Set₁ where
  zero : TypeSplit s t r
       → Γ -, s ∋[ zero ] t ▹ Γ -, r

  suc : Γ ∋[ i ] t ▹ Δ
      → Γ -, s ∋[ suc i ] t ▹ Δ -, s

exhaust : Type → Type
exhaust (Pure x) = Pure x
exhaust (Chan idx _ _ t) = Chan idx 0∙ 0∙ t
exhaust (Pair t f) = Pair (exhaust t) (exhaust f)

data _⊢_▹_ : Ctx n → Scoped n → Ctx n → Set₁ where
  𝟘 : Γ ⊢ 𝟘 ▹ Γ

  -- Note (μ , μ): the created channel is balanced
  ν : ∀ (idx : Idx) (μ : Usage idx) (t : Type)
    → Γ -, (Chan idx μ μ t) ⊢ P   ▹ Δ -, (Chan idx 0∙ 0∙ t)
    -----------------------------------------------------
    → Γ                     ⊢ ν P ▹ Δ

  _⦅⦆_ : Γ      ∋[ i ] (Chan idx 1∙ 0∙ t) ▹ Ξ
       → Ξ -, t ⊢ P                       ▹ Θ -, exhaust t
       -------------------------------------------------
       → Γ      ⊢ (i ⦅⦆ P)                ▹ Θ

  _⟨_⟩_ : Γ ∋[ i ] (Chan idx 0∙ 1∙ t) ▹ Δ
        → Δ ∋[ j ] t                  ▹ Ξ
        → Ξ ⊢ P                       ▹ Θ
        ------------------------------------
        → Γ ⊢ i ⟨ j ⟩ P               ▹ Θ

  _∥_ : Γ ⊢ P     ▹ Δ
      → Δ ⊢ Q     ▹ Ξ
      --------------
      → Γ ⊢ P ∥ Q ▹ Ξ

data CtxSplit : Ctx n → Ctx n → Ctx n → Set₁ where
  []  : CtxSplit [] [] []
  _∷_ : TypeSplit s t r
      → CtxSplit Γ Δ Θ
      → CtxSplit (s ∷ Γ) (t ∷ Δ) (r ∷ Θ)
