open import Relation.Nullary.Decidable using (True)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

import Data.Unit as Unit
import Data.Fin as Fin
import Data.Nat as Nat
import Data.Bool as Bool
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
open Unit using (⊤; tt)
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
infixr 4 _w_⊢_⊠_
infixr 4 _w_∋_w_⊠_
infixr 10 base chan recv send

pattern _-,_ Γ σ = σ ∷ Γ

-- Shapes

record Tree (A : Set) : Set where
  constructor <_&_>
  inductive
  field
    value : A
    children : Σ ℕ (Vec (Tree A))

Shape : Set
Shape = Tree ℕ

Shapes : ℕ → Set
Shapes = Vec Shape

-- Shapes interpreted as multiplicities

Card : Shape → Set
Card < v & _ > = Vec MType v

Cards : ∀ {n} → Shapes n → Set
Cards [] = ⊤
Cards (xs -, x) = Cards xs × Card x

Mult : (s : Shape) → Card s → Set
Mult _ = All ωℕ

Mults : ∀ {n} {ss : Shapes n} → Cards ss → Set
Mults {ss = []} tt = ⊤
Mults {ss = ss -, s} (cs , c) = Mults cs × Mult s c

ε : ∀ {n} {ss : Shapes n} {cs : Cards ss} → Mults cs
ε {ss = []} {tt} = tt
ε {ss = _ -, _} {_ , _} = ε , replicate ω0

data Type : Shape → Set where
  B[_]   : ℕ → Type < 0 & _ , [] >
  C[_w_] : {s : Shape} {c : Card s} → Type s → Mult s c → Type < 2 & _ , s ∷ [] >
  P[_&_] : {s r : Shape} → Type s → Type r → Type < 0 & _ , s ∷ r ∷ [] >

Types : ∀ {n} → Shapes n → Set
Types = All Type

private
  variable
    n : ℕ
    M N : MType
    P Q : Scoped n

data _w_∋_w_⊠_ : {ss : Shapes n} {cs : Cards ss} → Types ss → Mults cs
               → {s : Shape} {c : Card s} → Type s → Mult s c
               → Mults cs → Set where

  zero : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ : Mults cs}
       → {s : Shape} {c : Card s} {t : Type s} {m n : Mult s c}
       → γ -, t w Γ , (m +ᵥ n) ∋ t w n ⊠ Γ , m

  suc : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
      → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
      → {s' : Shape} {c' : Card s'} {t' : Type s'} {m' : Mult s' c'}
      → γ w Γ ∋ t w m ⊠ Δ
      → γ -, t' w Γ , m' ∋ t w m ⊠ Δ , m'

toFin : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
      → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
      → γ w Γ ∋ t w m ⊠ Δ
      → Fin n
toFin zero = zero
toFin (suc x) = suc (toFin x)

_↑_↓ : ωℕ M → ωℕ N → All ωℕ (N ∷ M ∷ [])
μ↑ ↑ μ↓ ↓ = μ↓ ∷ μ↑ ∷ []

data _w_⊢_⊠_ : {ss : Shapes n} {cs : Cards ss}
             → Types ss → Mults cs → Scoped n → Mults cs → Set where

  end : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ : Mults cs}
      → γ w Γ ⊢ 𝟘 ⊠ Γ

  base : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
       → {t : ℕ}
       → γ -, B[ t ] w Γ , [] ⊢ P     ⊠ Δ , []
       ---------------------------------------
       → γ           w Γ      ⊢ +[] P ⊠ Δ

  chan : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
       → {s : Shape} {c : Card s} (t : Type s) (m : Mult s c)
       → (μ : ωℕ M)
       → γ -, C[ t w m ] w Γ , μ ↑ μ ↓ ⊢ P     ⊠ Δ , ω0 ↑ ω0 ↓
       -------------------------------------------------------
       → γ               w Γ           ⊢ new P ⊠ Δ

  recv : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Ξ Θ : Mults cs}
       → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
       → (x : γ      w Γ      ∋ C[ t w m ] w (ω0 {M}) ↑ (ω1 {N}) ↓ ⊠ Ξ)
       →      γ -, t w Ξ , m  ⊢ P                                  ⊠ Θ , replicate ω0
       ------------------------------------------------------------------------------
       →      γ      w Γ      ⊢ toFin x ⦅⦆ P                       ⊠ Θ

  send : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ Ξ Θ : Mults cs}
       → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
       → (x : γ w Γ ∋ C[ t w m ] w ω1 {M} ↑ ω0 {N} ↓ ⊠ Δ)
       → (y : γ w Δ ∋ t          w  m                ⊠ Ξ)
       →      γ w Ξ ⊢ P                              ⊠ Θ
       -------------------------------------------------
       →      γ w Γ ⊢ toFin x ⟨ toFin y ⟩ P          ⊠ Θ

  comp : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ Ξ : Mults cs}
       → γ w Γ ⊢ P     ⊠ Δ
       → γ w Δ ⊢ Q     ⊠ Ξ
       -------------------
       → γ w Γ ⊢ P ∥ Q ⊠ Ξ

_w_⊢_ : {ss : Shapes n} {cs : Cards ss} → Types ss → Mults cs → Scoped n → Set
γ w Γ ⊢ P = γ w Γ ⊢ P ⊠ ε
