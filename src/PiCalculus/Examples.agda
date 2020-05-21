{-# OPTIONS --safe #-} -- --without-K #-}

open import Data.Nat using (ℕ)
open import Data.String.Base using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (#_; zero; suc)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Level as L

open import PiCalculus.Syntax
open Syntax
open Scoped
open Conversion
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Algebras
open import PiCalculus.LinearTypeSystem.Algebras.Linear using (Linear)
open import PiCalculus.LinearTypeSystem.Algebras.Shared using (Shared)

module PiCalculus.Examples where
open Raw

variable
  n : ℕ

raw : Raw tt
raw = ⦅υ "x"⦆ (("x" ⦅ "b" ⦆ 𝟘) ∥ ("x" ⟨ "a" ⟩ 𝟘))

scoped : Scoped 1
scoped = υ (((# 0) ⦅⦆ 𝟘) ∥ ((# 0) ⟨ # 1 ⟩ 𝟘))

_ : raw→scoped ("a" ∷ []) raw ≡ just scoped
_ = refl

channel-over-channel₀ : Raw tt
channel-over-channel₀ = ⦅υ "x"⦆
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ (⦅υ "z"⦆ ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘)))

channel-over-channel₁ : Raw tt
channel-over-channel₁ = ⦅υ "x"⦆ ⦅υ "z"⦆
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₂ : Raw tt
channel-over-channel₂ = ⦅υ "z"⦆ ⦅υ "x"⦆
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₃ : Raw tt
channel-over-channel₃ = ⦅υ "z"⦆ ⦅υ "x"⦆
                        ( ("z" ⦅ "p" ⦆ 𝟘)
                        ∥ ("z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₄ : Raw tt
channel-over-channel₄ = ⦅υ "z"⦆ ⦅υ "x"⦆
                        (𝟘 ∥ 𝟘)

channel-over-channel₅ : Raw tt
channel-over-channel₅ = ⦅υ "z"⦆ ⦅υ "x"⦆ 𝟘

channel-over-channel₆ : Raw tt
channel-over-channel₆ = ⦅υ "z"⦆ 𝟘

channel-over-channel₇ : Raw tt
channel-over-channel₇ = 𝟘

_raw-[_]≅_ : ∀ {n} → Raw tt → Vec String n → Raw tt → Set
P raw-[ Γ ]≅ Q with raw→scoped Γ P | raw→scoped Γ Q
P raw-[ Γ ]≅ Q | just sP | just sQ = Σ[ r ∈ RecTree ] sP ≅⟨ r ⟩ sQ
P raw-[ Γ ]≅ Q | _       | _       = ⊤

_raw-[_]⇒_ : ∀ {n} → Raw tt → Vec String n → Raw tt → Set
P raw-[ Γ ]⇒ Q with raw→scoped Γ P | raw→scoped Γ Q
P raw-[ Γ ]⇒ Q | just sP | just sQ = Σ[ c ∈ Channel _ ] (sP =[ c ]⇒ sQ)
P raw-[ Γ ]⇒ Q | _       | _       = ⊤

_ : channel-over-channel₀ raw-[ "y" ∷ [] ]≅ channel-over-channel₁
_ = _ , υ-cong cong-symm stop scope-ext ((λ ()) , (λ ()) , tt)

_ : channel-over-channel₁ raw-[ "y" ∷ [] ]≅ channel-over-channel₂
_ = _ , stop scope-scope-comm

_ : channel-over-channel₂ raw-[ "y" ∷ [] ]⇒ channel-over-channel₃
_ = _ , res res comm

_ : channel-over-channel₃ raw-[ "y" ∷ [] ]⇒ channel-over-channel₄
_ = _ , res res comm

_ : channel-over-channel₄ raw-[ "y" ∷ [] ]≅ channel-over-channel₅
_ = _ , υ-cong υ-cong stop comp-end

_ : channel-over-channel₅ raw-[ "y" ∷ [] ]≅ channel-over-channel₆
_ = _ , υ-cong stop scope-end

_ : channel-over-channel₆ raw-[ "y" ∷ [] ]≅ channel-over-channel₇
_ = _ , stop scope-end

module Shared-Linear where
  pattern LINEAR = true
  pattern SHARED = false
  pattern 0∙ = false
  pattern 1∙ = true

  QUANTIFIERS : Algebras
  Algebras.Idx QUANTIFIERS = Bool
  Algebras.∃Idx QUANTIFIERS = SHARED
  Algebras.Usage QUANTIFIERS SHARED = ⊤
  Algebras.Usage QUANTIFIERS LINEAR = Bool
  Algebras.UsageAlgebra QUANTIFIERS SHARED = Shared
  Algebras.UsageAlgebra QUANTIFIERS LINEAR = Linear

  open Algebras QUANTIFIERS hiding (ℓᵢ;ℓₒ;ℓ∅;ℓ#;0∙;1∙)
  open import PiCalculus.LinearTypeSystem QUANTIFIERS
  open import PiCalculus.LinearTypeSystem.ContextLemmas QUANTIFIERS

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

  _ : [] -, 𝟙 ∝[ [] -, SHARED ] [] -, ω∙ ⊢ υ ((zero ⟨ suc zero ⟩ 𝟘) ∥ (zero ⦅⦆ 𝟘)) ⊠ ε
  _ = chan 𝟙 ω∙ {LINEAR} 1∙
      (comp (send here (there here) end)
      (recv here end))

  p : Scoped 1
  p = υ ((zero ⦅⦆ (zero ⦅⦆ 𝟘)) ∥ (υ (suc zero ⟨ zero ⟩ zero ⟨ suc (suc zero) ⟩ 𝟘)))

  _ : [] -, 𝟙 ∝[ [] -, SHARED ] [] -, ω∙ ⊢ p ⊠ ε
  _ = chan C[ 𝟙 ∝ ω∙ ] {LINEAR} ℓᵢ {LINEAR} 1∙ (comp
           (recv here (recv here end))
           (chan 𝟙 ω∙ 1∙
                 (send (there here) here (send here (there there here) end))))


module Linear where
  QUANTIFIERS : Algebras
  Algebras.Idx QUANTIFIERS = ⊤
  Algebras.∃Idx QUANTIFIERS = tt
  Algebras.Usage QUANTIFIERS _ = Bool
  Algebras.UsageAlgebra QUANTIFIERS _ = Linear

  open Algebras QUANTIFIERS
  open import PiCalculus.LinearTypeSystem QUANTIFIERS

  _ : [] -, C[ 𝟙 ∝ ℓᵢ ] -, 𝟙 ∝ [] -, ℓ# -, ℓ# ∋[ suc zero ] C[ 𝟙 ∝ ℓᵢ ] ∝ ℓᵢ ⊠ [] -, ℓₒ -, ℓ#
  _ = there here

