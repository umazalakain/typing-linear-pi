open import Relation.Nullary.Decidable using (True)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

import Data.Fin as Fin
import Data.Nat as Nat
import Data.Bool as Bool
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
open Nat using (ℕ; zero; suc)
open Fin using (Fin; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)

open import PiCalculus.Syntax
open Syntax
open Scoped
open import PiCalculus.LinearTypeSystem.OmegaNat

module PiCalculus.LinearTypeSystem where


infix 50 _↑_↓
infixl 20 _-,_
infixr 5 _w_⊢_⊠_
infixr 5 _w_∋_w_⊠_
infixr 10 base chan recv send

-- Shapes

record Tree (A : Set) : Set where
  constructor <_&_>
  inductive
  field
    value : A
    children : Σ ℕ (Vec (Tree A))

Shape : Set
Shape = Tree ℕ

SCtx : ℕ → Set
SCtx = Vec Shape

-- Shapes interpreted as multiplicities

Capability : Shape → Set
Capability < n & _ > = Vec ωℕ n

CCtx : ∀ {n} → SCtx n → Set
CCtx = All Capability

-- Shapes interpreted as types

data Type : Shape → Set where
  B[_]   : ℕ → Type < 0 & _ , [] >
  C[_w_] : ∀ {s : Shape} → Type s → Capability s → Type < 2 & _ , s ∷ [] >
  P[_&_] : ∀ {s r : Shape} → Type s → Type r → Type < 0 & _ , s ∷ r ∷ [] >

TCtx : ∀ {n} → SCtx n → Set
TCtx = All Type

pattern _-,_ Γ σ = σ ∷ Γ

private
  variable
    n : ℕ
    i : Fin n
    s : Shape
    t : Type s
    c : Capability s
    ss : SCtx n
    γ : TCtx ss
    Γ Δ ϕ Κ : CCtx ss
    P Q : Scoped n

data _w_∋_w_⊠_ : {ss : SCtx n} → TCtx ss → CCtx ss
               → {s : Shape} → Type s → Capability s
               → CCtx ss
               → Set where

  -- Let Γ ⊢ P ⊠ Δ and Δ ⊢ Q ⊠ ϕ. Additionally, assume P preserves ω∙ resources,
  -- but Q downgrades ω∙ resources into 1∙ -- possible because ω∙ + 1∙ ≡ ω∙.
  -- Then Γ ⊢ P ∥ Q ⊠ ϕ but Γ ⊬ Q ∥ P ⊠ ϕ.
  -- Therefore ω∙ resources must be preserved.

  zero : {ss : SCtx n} {γ : TCtx ss} {Γ : CCtx ss}
       → {s : Shape} {t : Type s} {ms ns : Capability s}
       -- Prevent ns from introducing ω
       → ⦃ p : True (ωᵥ? (ms +ᵥ ns) ms) ⦄
       → γ -, t w Γ -, (ms +ᵥ ns) ∋ t w ns ⊠ Γ -, ms

  suc : {ss : SCtx n} {γ : TCtx ss} {Γ Δ : CCtx ss}
      → {s : Shape} {t : Type s} {c : Capability s}
      → {s' : Shape} {t' : Type s'} {c' : Capability s'}
      → γ       w Γ       ∋ t w c ⊠ Δ
      → γ -, t' w Γ -, c' ∋ t w c ⊠ Δ -, c'

toFin : {ss : SCtx n} {γ : TCtx ss} {Γ Δ : CCtx ss}
      → {s : Shape} {t : Type s} {c : Capability s}
      → γ w Γ ∋ t w c ⊠ Δ
      → Fin n
toFin zero = zero
toFin (suc x) = suc (toFin x)

_↑_↓ : ωℕ → ωℕ → Vec ωℕ 2
μ↑ ↑ μ↓ ↓ = μ↓ ∷ μ↑ ∷ []

data _w_⊢_⊠_ : {ss : SCtx n} → TCtx ss → CCtx ss → Scoped n → CCtx ss → Set where
  end : γ w Γ ⊢ 𝟘 ⊠ Γ

  base : {n : ℕ}
       → γ -, B[ n ] w Γ -, [] ⊢ P     ⊠ Δ -, []
       -----------------------------------------
       → γ           w Γ       ⊢ +[] P ⊠ Δ

  chan : {s : Shape} (t : Type s) (c : Capability s)
       → (μ : ωℕ)
       → let μs = Vec.replicate μ in
         γ -, C[ t w c ] w Γ -, μs ⊢ P     ⊠ Δ -, (μs ∸ᵥ μs)
       -----------------------------------------------------
       → γ               w Γ       ⊢ new P ⊠ Δ

  recv : {ss : SCtx n} {γ : TCtx ss} {Γ Δ ϕ : CCtx ss}
       → {s : Shape} {t : Type s} {c : Capability s}
       → (x : γ      w Γ      ∋ C[ t w c ] w 1∙ ↑ 0∙ ↓ ⊠ Δ)
       →      γ -, t w Δ -, c ⊢ P                      ⊠ ϕ -, (c ∸ᵥ c)
       ---------------------------------------------------------------
       →      γ      w Γ      ⊢ toFin x ⦅⦆ P           ⊠ ϕ

  send : {s : Shape} {t : Type s} {c : Capability s}
       → (x : γ w Γ ∋ C[ t w c ] w 0∙ ↑ 1∙ ↓ ⊠ Δ)
       → (y : γ w Δ ∋ t          w c         ⊠ ϕ)
       →      γ w ϕ ⊢ P                      ⊠ Κ
       ------------------------------------------
       →      γ w Γ ⊢ toFin x ⟨ toFin y ⟩ P  ⊠ Κ

  comp : γ w Γ ⊢ P     ⊠ Δ
       → γ w Δ ⊢ Q     ⊠ ϕ
       ----------------------------
       → γ w Γ ⊢ P ∥ Q ⊠ ϕ

_w_⊢_ : {ss : SCtx n} → TCtx ss → CCtx ss → Scoped n → Set
γ w Γ ⊢ P = γ w Γ ⊢ P ⊠ All.map (Vec.map consume) Γ -- FIXME: Γ / Γ
