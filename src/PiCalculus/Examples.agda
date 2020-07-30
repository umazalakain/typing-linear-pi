{-# OPTIONS --safe #-} -- --without-K #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (zero; suc) renaming (#_ to #'_)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Level as L

open import PiCalculus.Syntax
open Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Algebras
open import PiCalculus.LinearTypeSystem.Algebras.Linear using (Linear)
open import PiCalculus.LinearTypeSystem.Algebras.Shared using (Shared)
open import PiCalculus.LinearTypeSystem.Algebras.Graded using (Graded)

module PiCalculus.Examples where
open Raw

variable
  n : ℕ

raw : Raw
raw = ⦅ν "x"⦆ (("x" ⦅ "y" ∷ [] ⦆ 𝟘) ∥ ("x" ⟨ "a" ∷ [] ⟩ 𝟘))

scoped : Scoped 1
scoped = ν (((#' 0) ⦅ 1 ⦆ 𝟘) ⦃ "y" ∷ [] ⦄ ∥ ((#' 0) ⟨ #' 1 ∷ [] ⟩ 𝟘)) ⦃ "x" ⦄

_ : Conversion.fromRaw ("a" ∷ []) raw ≡ scoped
_ = refl


channel-over-channel₀ : Raw
channel-over-channel₀ = ⦅ν "x"⦆
                        ( ("x" ⦅ "r" ∷ [] ⦆ "r" ⦅ "p" ∷ [] ⦆ 𝟘)
                        ∥ (⦅ν "z"⦆ ("x" ⟨ "z" ∷ [] ⟩ "z" ⟨ "y" ∷ [] ⟩ 𝟘)))

channel-over-channel₁ : Raw
channel-over-channel₁ = ⦅ν "x"⦆ ⦅ν "z"⦆
                        ( ("x" ⦅ "r" ∷ [] ⦆ "r" ⦅ "p" ∷ [] ⦆ 𝟘)
                        ∥ ("x" ⟨ "z" ∷ [] ⟩ "z" ⟨ "y" ∷ [] ⟩ 𝟘))

channel-over-channel₂ : Raw
channel-over-channel₂ = ⦅ν "z"⦆ ⦅ν "x"⦆
                        ( ("x" ⦅ "r" ∷ [] ⦆ "r" ⦅ "p" ∷ [] ⦆ 𝟘)
                        ∥ ("x" ⟨ "z" ∷ [] ⟩ "z" ⟨ "y" ∷ [] ⟩ 𝟘))

channel-over-channel₃ : Raw
channel-over-channel₃ = ⦅ν "z"⦆ ⦅ν "x"⦆
                        ( ("z" ⦅ "p" ∷ [] ⦆ 𝟘)
                        ∥ ("z" ⟨ "y" ∷ [] ⟩ 𝟘))

channel-over-channel₄ : Raw
channel-over-channel₄ = ⦅ν "z"⦆ ⦅ν "x"⦆
                        (𝟘 ∥ 𝟘)

channel-over-channel₅ : Raw
channel-over-channel₅ = ⦅ν "z"⦆ ⦅ν "x"⦆ 𝟘

channel-over-channel₆ : Raw
channel-over-channel₆ = ⦅ν "z"⦆ 𝟘

channel-over-channel₇ : Raw
channel-over-channel₇ = 𝟘

_!_≅_ : ∀ {n} → Vec Name n → Raw → Raw → Set
_!_≅_ = Conversion.fmap₂ _≅_

_!_⇒_ : ∀ {n} → Vec Name n → Raw → Raw → Set
_!_⇒_ = Conversion.fmap₂ _⇒_

_ : ("y" ∷ []) ! channel-over-channel₀ ≅ channel-over-channel₁
_ = _ , ν-cong cong-symm stop scope-ext (tt , tt , tt)

_ : ("y" ∷ []) ! channel-over-channel₁ ≅ channel-over-channel₂
_ = _ , stop scope-scope-comm

_ : ("y" ∷ []) ! channel-over-channel₂ ⇒ channel-over-channel₃
_ = _ , res res comm

_ : ("y" ∷ []) ! channel-over-channel₃ ⇒ channel-over-channel₄
_ = _ , res res comm

_ : ("y" ∷ []) ! channel-over-channel₄ ≅ channel-over-channel₅
_ = _ , ν-cong ν-cong stop comp-end

_ : ("y" ∷ []) ! channel-over-channel₅ ≅ channel-over-channel₆
_ = _ , ν-cong stop scope-end

_ : ("y" ∷ []) ! channel-over-channel₆ ≅ channel-over-channel₇
_ = _ , stop scope-end

{-
module Shared-Graded-Linear where
  data Usage : Set where
    sha gra lin : Usage

  pattern 0∙ = false
  pattern 1∙ = true

  QUANTIFIERS : Algebras
  Algebras.Idx QUANTIFIERS = Usage
  Algebras.∃Idx QUANTIFIERS = sha
  Algebras.Usage QUANTIFIERS sha = ⊤
  Algebras.Usage QUANTIFIERS gra = ℕ
  Algebras.Usage QUANTIFIERS lin = Bool
  Algebras.UsageAlgebra QUANTIFIERS sha = Shared
  Algebras.UsageAlgebra QUANTIFIERS gra = Graded
  Algebras.UsageAlgebra QUANTIFIERS lin = Linear

  open Algebras QUANTIFIERS hiding (ℓᵢ;ℓₒ;ℓ∅;ℓ#;0∙;1∙)
  open import PiCalculus.LinearTypeSystem QUANTIFIERS
  open import PiCalculus.LinearTypeSystem.ContextLemmas QUANTIFIERS

  _!_；[_]_⊢_▹_ : Vec Name n → PreCtx n → (idxs : Idxs n) → Ctx idxs → Raw → Ctx idxs → Set
  ctx ! γ ；[ idxs ] Γ ⊢ P ▹ Δ = Conversion.map (λ P' → γ ；[ idxs ] Γ ⊢ P' ▹ Δ) ctx P

  ω∙ : ⊤ ²
  ω∙ = tt , tt

  ℓ# : Bool ²
  ℓ# = true , true

  ℓᵢ : Bool ²
  ℓᵢ = true , false

  ℓₒ : Bool ²
  ℓₒ = false , true

  ℓ∅ : Bool ²
  ℓ∅ = false , false

  instance
    name : Name
    name = ""

  _ : ([] -, "y") ! [] -, 𝟙 ；[ [] -, sha ] [] -, ω∙ ⊢ channel-over-channel₀ ▹ ε
  _ = ν C[ 𝟙 ； ω∙ ] ℓᵢ {lin} 1∙
      (((here ) ⦅⦆ (here ⦅⦆ 𝟘)) ∥
            (ν 𝟙 ω∙ {lin} 1∙
                  ((there here) ⟨ here ⟩ (here ⟨ there there here ⟩ 𝟘))))

  _ : [] -, 𝟙 ；[ [] -, sha ] [] -, ω∙ ⊢ ν (((#' 0) ⟨ #' 1 ⟩ 𝟘) ∥ ((#' 0) ⦅⦆ 𝟘)) ▹ ε
  _ = ν 𝟙 ω∙ {lin} 1∙ ((# 0 ⟨ # 1 ⟩ 𝟘) ∥ (# 0 ⦅⦆ 𝟘))

  p : Scoped 1
  p = ν (((#' 0) ⦅⦆ ((#' 0) ⦅⦆ 𝟘)) ∥ (ν ((#' 1) ⟨ #' 0 ⟩ (#' 0) ⟨ #' 2 ⟩ 𝟘)))

  _ : [] -, 𝟙 ；[ [] -, sha ] [] -, ω∙ ⊢ p ▹ ε
  _ = ν C[ 𝟙 ； ω∙ ] {lin} ℓᵢ {lin} 1∙ (
           (here ⦅⦆ (here ⦅⦆ 𝟘)) ∥ (ν 𝟙 ω∙ 1∙ (there here ⟨ here ⟩ (here ⟨ there there here ⟩ 𝟘))))

  P : Scoped 2
  P = (ν (suc zero ⟨ zero ⟩ zero ⟨ suc (suc zero) ⟩ 𝟘)) ∥ (zero ⦅⦆ zero ⦅⦆ 𝟘)

  ⊢P : ∀ {n} → [] -, 𝟙 -, C[ C[ 𝟙 ； ω∙ ] ； ℓᵢ ] ；[ [] -, sha -, gra ] [] -, ω∙ -, (suc n , suc n) ⊢ P ▹ [] -, ω∙ -, (n , n)
  ⊢P = ν 𝟙 ω∙ {lin} 1∙ ((there here) ⟨ here ⟩ (here ⟨ there there here ⟩ 𝟘)) ∥ (here ⦅⦆ (here ⦅⦆ 𝟘))

  ⊢P∥P : [] -, 𝟙 ；[ [] -, sha ] [] -, ω∙ ⊢ ν (P ∥ P) ▹ ε
  ⊢P∥P = ν C[ 𝟙 ； ω∙ ] ℓᵢ 2 (⊢P ∥ ⊢P)

module Linear where
  QUANTIFIERS : Algebras
  Algebras.Idx QUANTIFIERS = ⊤
  Algebras.∃Idx QUANTIFIERS = tt
  Algebras.Usage QUANTIFIERS _ = Bool
  Algebras.UsageAlgebra QUANTIFIERS _ = Linear

  open Algebras QUANTIFIERS
  open import PiCalculus.LinearTypeSystem QUANTIFIERS
  open import PiCalculus.LinearTypeSystem.ContextLemmas QUANTIFIERS

  _ : [] -, C[ 𝟙 ； ℓᵢ ] -, 𝟙 ； [] -, ℓ# -, ℓ# ∋[ #' 1 ] C[ 𝟙 ； ℓᵢ ] ； ℓᵢ ▹ [] -, ℓₒ -, ℓ#
  _ = there here
-}
