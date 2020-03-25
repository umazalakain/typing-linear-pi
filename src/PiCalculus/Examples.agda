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
open Raw
open Scoped
open Conversion
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Quantifiers
open import PiCalculus.LinearTypeSystem.Quantifiers.Linear
open import PiCalculus.LinearTypeSystem.Quantifiers.Shared

module PiCalculus.Examples where

QUANTIFIERS : Quantifiers
Quantifiers.I QUANTIFIERS = Bool
Quantifiers.∃I QUANTIFIERS = false
Quantifiers.Cs QUANTIFIERS false = Ω
Quantifiers.Cs QUANTIFIERS true = Mult
Quantifiers.Qs QUANTIFIERS false = Shared
Quantifiers.Qs QUANTIFIERS true = Linear

open Quantifiers QUANTIFIERS

open import PiCalculus.LinearTypeSystem QUANTIFIERS

variable
  n : ℕ

raw : Raw tt
raw = ⦅new "x"⦆ (("x" ⦅ "b" ⦆ 𝟘) ∥ ("x" ⟨ "a" ⟩ 𝟘))

scoped : Scoped 1
scoped = new (((# 0) ⦅⦆ 𝟘) ∥ ((# 0) ⟨ # 1 ⟩ 𝟘))

_ : raw→scoped ("a" ∷ []) raw ≡ just scoped
_ = refl

channel-over-channel₀ : Raw tt
channel-over-channel₀ = ⦅new "x"⦆
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ (⦅new "z"⦆ ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘)))

channel-over-channel₁ : Raw tt
channel-over-channel₁ = ⦅new "x"⦆ ⦅new "z"⦆
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₂ : Raw tt
channel-over-channel₂ = ⦅new "z"⦆ ⦅new "x"⦆
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₃ : Raw tt
channel-over-channel₃ = ⦅new "z"⦆ ⦅new "x"⦆
                        ( ("z" ⦅ "p" ⦆ 𝟘)
                        ∥ ("z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₄ : Raw tt
channel-over-channel₄ = ⦅new "z"⦆ ⦅new "x"⦆
                        (𝟘 ∥ 𝟘)

channel-over-channel₅ : Raw tt
channel-over-channel₅ = ⦅new "z"⦆ ⦅new "x"⦆ 𝟘

channel-over-channel₆ : Raw tt
channel-over-channel₆ = ⦅new "z"⦆ 𝟘

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
_ = _ , new-cong cong-symm stop scope-ext ((λ ()) , (λ ()) , tt)

_ : channel-over-channel₁ raw-[ "y" ∷ [] ]≅ channel-over-channel₂
_ = _ , stop scope-scope-comm

_ : channel-over-channel₂ raw-[ "y" ∷ [] ]⇒ channel-over-channel₃
_ = _ , res res comm

_ : channel-over-channel₃ raw-[ "y" ∷ [] ]⇒ channel-over-channel₄
_ = _ , res res comm

_ : channel-over-channel₄ raw-[ "y" ∷ [] ]≅ channel-over-channel₅
_ = _ , new-cong new-cong stop comp-end

_ : channel-over-channel₅ raw-[ "y" ∷ [] ]≅ channel-over-channel₆
_ = _ , new-cong stop scope-end

_ : channel-over-channel₆ raw-[ "y" ∷ [] ]≅ channel-over-channel₇
_ = _ , stop scope-end

raw-[_]_∝_⊢_ : ∀ {n} → Vec String n → Vec Type n → {idxs : Vec I n} → All Cs idxs → Raw tt → Set
raw-[ names ] γ ∝ Γ ⊢ P with raw→scoped names P
raw-[ names ] γ ∝ Γ ⊢ P | just P' = γ ∝ Γ ⊢ P'
raw-[ names ] γ ∝ Γ ⊢ P | nothing = L.Lift _ ⊤

_ : raw-[ [] -, "a" ] [] -, B[ 0 ] ∝ _∷_ {x = false} ω∙ [] ⊢ (⦅new "x" ⦆ (("x" ⟨ "a" ⟩ 𝟘)) ∥ ("x" ⦅ "b" ⦆ 𝟘))
_ = chan {idx = true} B[ 0 ] ω∙ Mult.ℓ# (comp (send zero (suc zero) end) (recv zero end))

_ : raw-[ [] -, "y" ] [] -, B[ 0 ] ∝ _∷_ {x = false} ω∙ [] ⊢ channel-over-channel₀
_ = chan {idx' = true} {idx = true} C[ B[ 0 ] ∝ ω∙ ] Mult.ℓᵢ Mult.ℓ# (comp
         (recv zero (recv zero end))
         (chan B[ 0 ] ω∙ Mult.ℓ# (send (suc zero) zero (send zero (suc (suc zero)) end))))
