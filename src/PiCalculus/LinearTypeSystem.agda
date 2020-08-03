{-# OPTIONS --safe --without-K #-}

open import Relation.Nullary.Decidable using (True; toWitness)
open import Function using (_∘_)

open import Data.Product as Product using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit as Unit using (⊤; tt)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; map; length; _++_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.All.Properties renaming (++⁺ to _++⁺_)

open import PiCalculus.Syntax
open Scoped
open import PiCalculus.LinearTypeSystem.Algebras

module PiCalculus.LinearTypeSystem (Ω : Algebras) where
open Algebras Ω

infixr 4 _；_⊢_▹_
infixr 4 _∋[_]_▹_ _∋[_]_
infixr 10 ν _⦅⦆_ _⟨_⟩_

private
  variable
    n m : ℕ
    nx : Name
    ns : Vec Name n
    idx idx' : Idx
    i j : Fin n
    js : Vec (Fin n) m

data Type : Set

TypeUsage : Set
TypeUsage = Type × ∃[ idx ] (Usage idx ²)

data Type where
  C[_] : Vec TypeUsage m → Type

types : Vec TypeUsage m → Vec Type m
types = map proj₁

usages : (xs : Vec TypeUsage m) → All (λ idx → Usage idx ²) (map (proj₁ ∘ proj₂) xs )
usages [] = []
usages (xs -, (_ , (_ , u))) = usages xs -, u

-- Context of types
PreCtx : ℕ → Set
PreCtx = Vec Type

-- Context of usage indices
Idxs : ℕ → Set
Idxs = Vec Idx

-- Indexed context of usages
Ctx : ∀ {n} → Idxs n → Set
Ctx = All λ idx → Usage idx ²

ε : ∀ {n} {idxs : Idxs n} → Ctx idxs
ε {idxs = []} = []
ε {idxs = idxs -, x} = ε -, ℓ∅

private
  variable
    γ : PreCtx n
    idxs idxs' : Idxs n
    Γ Δ Ξ Θ : Ctx idxs
    b : ℕ
    t t' : Type
    x y z : Usage idx
    P Q : Scoped n

-- γ ∋[ i ] t is a proof that variable i in Γ has type t
data _∋[_]_ : PreCtx n → Fin n → Type → Set where
  zero : γ -, t ∋[ zero ] t
  suc : γ ∋[ i ] t → γ -,  t' ∋[ suc i ] t

data _⊇[_]_ : PreCtx n → Vec (Fin n) m → Vec Type m → Set where
  [] : γ ⊇[ [] ] []
  _∷_ : ∀ {ts} → γ ∋[ j ] t → γ ⊇[ js ] ts → γ ⊇[ js -, j ] (ts -, t)


-- Γ ∋[ i ] x ▹ Δ is a proof that subtracting x from variable in in Γ results in Δ
data _∋[_]_▹_ : {idxs : Idxs n} → Ctx idxs → Fin n → Usage idx ² → Ctx idxs → Set where

  zero : {Γ : Ctx idxs} {x y z : Usage idx ²}
       → x ≔ y ∙² z
       → Γ -, x ∋[ zero {n} ] y ▹ Γ -, z

  suc : {Γ Δ : Ctx idxs} {x : Usage idx ² } {x' : Usage idx' ²}
      → Γ ∋[ i ] x ▹ Δ
      → Γ -, x' ∋[ suc i ] x ▹ Δ -, x'


data _⊇[_]_▹_ : {idxs : Idxs n} {idxs' : Idxs m} → Ctx idxs → Vec (Fin n) m → All (λ idx → Usage idx ²) idxs' → Ctx idxs → Set where
  [] : _⊇[_]_▹_ Γ [] [] Γ
  _,_ : ∀ {u : Usage idx ²} {us : Ctx idxs'} → Γ ⊇[ js ] us ▹ Δ → Δ ∋[ j ] u ▹ Ξ → Γ ⊇[ js -, j ] us -, u ▹ Ξ


module _ where
  infixr 4 _；_∋[_]_；_▹_

  -- For convenience, merge together γ ∋[ i ] t and Γ ∋[ i ] x ▹ Δ
  _；_∋[_]_；_▹_ : {idxs : Idxs n} → PreCtx n → Ctx idxs → Fin n → Type → Usage idx ² → Ctx idxs → Set
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


module _ where
  -- For convenience, merge together γ ⊇[ i ] t and Γ ⊇[ i ] x ▹ Δ
  _；_⊇[_]_▹_ : {idxs : Idxs n} → PreCtx n → Ctx idxs → Vec (Fin n) m → Vec TypeUsage m → Ctx idxs → Set
  γ ； Γ ⊇[ js ] ts ▹ Δ = (γ ⊇[ js ] types ts) × (Γ ⊇[ js ] usages ts ▹ Δ)


-- Typing judgment γ ； Γ ⊢ P ▹ Δ where P is a well-typed process
-- under typing context γ and input and output usage contexts Γ and Δ
data _；_⊢_▹_ : {idxs : Idxs n} → PreCtx n → Ctx idxs → Scoped n → Ctx idxs → Set where

  𝟘 : γ ； Γ ⊢ 𝟘 ▹ Γ

  -- Note (μ , μ): the created channel is balanced
  ν : ∀ (ts : Vec TypeUsage m) {idx : Idx} (μ : Usage idx)
    → γ -, C[ ts ] ； Γ -, (μ , μ) ⊢ P          ▹ Δ -, ℓ∅
    -----------------------------------------------------
    → γ            ； Γ            ⊢ ν P ⦃ nx ⦄ ▹ Δ

  _⦅⦆_ : ∀ {ts : Vec TypeUsage m} {Γ Ξ Θ : Ctx idxs}
       → γ             ； Γ                ∋[ i ] C[ ts ] ； ℓᵢ {idx}   ▹ Ξ
       → γ ++ types ts ； Ξ ++⁺ usages ts  ⊢      P                     ▹ Θ ++⁺ ε
       ------------------------------------------------------------------------
       → γ             ； Γ                ⊢ (i ⦅ length ts ⦆ P) ⦃ ns ⦄ ▹ Θ

  _⟨_⟩_ : {ts : Vec TypeUsage m}
        → γ ； Γ ∋[ i ]  C[ ts ] ； ℓₒ {idx} ▹ Δ
        → γ ； Δ ⊇[ js ] ts                  ▹ Ξ
        → γ ； Ξ ⊢       P                   ▹ Θ
        ----------------------------------------
        → γ ； Γ ⊢       i ⟨ js ⟩ P          ▹ Θ

  _∥_ : γ ； Γ ⊢ P     ▹ Δ
      → γ ； Δ ⊢ Q     ▹ Ξ
      --------------------
      → γ ； Γ ⊢ P ∥ Q ▹ Ξ

_；[_]_⊢_▹_ : PreCtx n → (idxs : Idxs n) → Ctx idxs → Scoped n → Ctx idxs → Set
γ ；[ idxs ] Γ ⊢ P ▹ Δ = _；_⊢_▹_ {idxs = idxs} γ Γ P Δ
