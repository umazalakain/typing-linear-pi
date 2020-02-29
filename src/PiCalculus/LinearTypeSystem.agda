open import Relation.Nullary.Decidable using (True; toWitness)

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
    n : ℕ

-- Shapes

record Tree (A : Set) : Set where
  constructor <_&_>
  inductive
  field
    value : A
    children : Σ ℕ (Vec (Tree A))

Shape : Set
Shape = Tree (ℕ × I)

Shapes : ℕ → Set
Shapes = Vec Shape

-- Shapes interpreted as multiplicities

Mult : Shape → Set
Mult < n , i & _ > = Vec (Cs i) n

Mults : ∀ {n} → Shapes n → Set
Mults = All Mult

ε : ∀ {n} {ss : Shapes n} → Mults ss
ε {ss = []} = []
ε {ss = _ -, _} = ε -, Vec.replicate 0∙

data Type : Shape → Set where
  B[_]   : ℕ → Type < 0 , ∃I & _ , [] >
  C[_w_] : ∀ {s i} → Type s → Mult s → Type < 2 , i & _ , s ∷ [] >
  P[_&_] : ∀ {s r} → Type s → Type r → Type < 0 , ∃I & _ , s ∷ r ∷ [] >

Types : ∀ {n} → Shapes n → Set
Types = All Type

data _w_∋_w_⊠_ : {ss : Shapes n} → Types ss → Mults ss
               → {s : Shape} → Type s → Mult s
               → Mults ss → Set where

  zero : {ss : Shapes n} {γ : Types ss} {Γ : Mults ss}
       → {s : Shape} {t : Type s} {ys zs : Mult s}
       → {check : True (∙ᵥ-compute ys zs)}
       → γ -, t w Γ -, proj₁ (toWitness check) ∋ t w ys ⊠ Γ -, zs

  suc : {ss : Shapes n} {γ : Types ss} {Γ Δ : Mults ss}
      → {s : Shape} {t : Type s} {m : Mult s}
      → {s' : Shape} {t' : Type s'} {m' : Mult s'}
      → γ w Γ ∋ t w m ⊠ Δ
      → γ -, t' w Γ -, m' ∋ t w m ⊠ Δ -, m'

toFin : {ss : Shapes n} {γ : Types ss} {Γ Δ : Mults ss}
      → {s : Shape} {t : Type s} {m : Mult s}
      → γ w Γ ∋ t w m ⊠ Δ
      → Fin n
toFin zero = zero
toFin (suc x) = suc (toFin x)

private
  variable
    i : I
    ss : Shapes n
    γ : Types ss
    Γ Δ Ξ Θ : Mults ss
    b : ℕ
    s : Shape
    t : Type s
    m : Mult s
    P Q : Scoped n

_↑_↓ : Cs i → Cs i → Vec (Cs i) 2
μ↑ ↑ μ↓ ↓ = μ↓ ∷ μ↑ ∷ []

data _w_⊢_⊠_ : {ss : Shapes n} → Types ss → Mults ss → Scoped n → Mults ss → Set where

  end : γ w Γ ⊢ 𝟘 ⊠ Γ

  base : γ -, B[ b ] w Γ -, [] ⊢ P     ⊠ Δ -, []
       -----------------------------------------
       → γ           w Γ       ⊢ +[] P ⊠ Δ

  chan : (t : Type s) (m : Mult s) (μ : Cs i)
       → γ -, C[ t w m ] w Γ -, μ ↑ μ ↓ ⊢ P     ⊠ Δ -, 0∙ ↑ 0∙ ↓
       ---------------------------------------------------------
       → γ               w Γ            ⊢ new P ⊠ Δ

  recv : {t : Type s} {m : Mult s}
       → (x : γ      w Γ       ∋ C[ t w m ] w 0∙ {i} ↑ 1∙ ↓ ⊠ Ξ)
       →      γ -, t w Ξ -, m  ⊢ P                          ⊠ Θ -, Vec.replicate 0∙
       ----------------------------------------------------------------------------
       →      γ      w Γ       ⊢ toFin x ⦅⦆ P               ⊠ Θ

  send : {t : Type s} {m : Mult s}
       → (x : γ w Γ ∋ C[ t w m ] w 1∙ {i} ↑ 0∙ ↓ ⊠ Δ)
       → (y : γ w Δ ∋ t          w m             ⊠ Ξ)
       →      γ w Ξ ⊢ P                          ⊠ Θ
       ---------------------------------------------
       →      γ w Γ ⊢ toFin x ⟨ toFin y ⟩ P      ⊠ Θ

  comp : γ w Γ ⊢ P     ⊠ Δ
       → γ w Δ ⊢ Q     ⊠ Ξ
       -------------------
       → γ w Γ ⊢ P ∥ Q ⊠ Ξ

_w_⊢_ : {ss : Shapes n} → Types ss → Mults ss → Scoped n → Set
γ w Γ ⊢ P = γ w Γ ⊢ P ⊠ ε
