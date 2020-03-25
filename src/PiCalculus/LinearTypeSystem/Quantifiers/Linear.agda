open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)

import Data.Unit as Unit
import Data.Product as Product
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open Unit using (⊤; tt)
open Product using (∃-syntax; _×_; _,_)
open ℕ using (ℕ)

open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Quantifiers.Linear where

data Mult : Set where
  ℓ∅ ℓᵢ ℓₒ ℓ# : Mult

data _≔_∙_ : Mult → Mult → Mult → Set where
  0≔ : ℓ∅ ≔ ℓ∅ ∙ ℓ∅
  1≔ˡ : ℓ# ≔ ℓ# ∙ ℓ∅
  1≔ʳ : ℓ# ≔ ℓ∅ ∙ ℓ#
  +≔ˡ : ℓᵢ ≔ ℓᵢ ∙ ℓ∅
  +≔ʳ : ℓᵢ ≔ ℓ∅ ∙ ℓᵢ
  -≔ˡ : ℓₒ ≔ ℓₒ ∙ ℓ∅
  -≔ʳ : ℓₒ ≔ ℓ∅ ∙ ℓₒ
  splitˡ : ℓ# ≔ ℓᵢ ∙ ℓₒ
  splitʳ : ℓ# ≔ ℓₒ ∙ ℓᵢ

∙-compute : ∀ y z → Dec (∃[ x ] (x ≔ y ∙ z))
∙-compute ℓ∅ ℓ∅ = yes (ℓ∅ , 0≔)
∙-compute ℓ∅ ℓᵢ = yes (ℓᵢ , +≔ʳ)
∙-compute ℓ∅ ℓₒ = yes (ℓₒ , -≔ʳ)
∙-compute ℓ∅ ℓ# = yes (ℓ# , 1≔ʳ)
∙-compute ℓᵢ ℓ∅ = yes (ℓᵢ , +≔ˡ)
∙-compute ℓᵢ ℓᵢ = no λ ()
∙-compute ℓᵢ ℓₒ = yes (ℓ# , splitˡ)
∙-compute ℓᵢ ℓ# = no λ ()
∙-compute ℓₒ ℓ∅ = yes (ℓₒ , -≔ˡ)
∙-compute ℓₒ ℓᵢ = yes (ℓ# , splitʳ)
∙-compute ℓₒ ℓₒ = no λ ()
∙-compute ℓₒ ℓ# = no λ ()
∙-compute ℓ# ℓ∅ = yes (ℓ# , 1≔ˡ)
∙-compute ℓ# ℓᵢ = no λ ()
∙-compute ℓ# ℓₒ = no λ ()
∙-compute ℓ# ℓ# = no λ ()

∙-computeˡ : ∀ x z → Dec (∃[ y ] (x ≔ y ∙ z))
∙-computeˡ ℓ∅ ℓ∅ = yes (ℓ∅ , 0≔)
∙-computeˡ ℓ∅ ℓᵢ = no λ ()
∙-computeˡ ℓ∅ ℓₒ = no λ ()
∙-computeˡ ℓ∅ ℓ# = no λ ()
∙-computeˡ ℓᵢ ℓ∅ = yes (ℓᵢ , +≔ˡ)
∙-computeˡ ℓᵢ ℓᵢ = yes (ℓ∅ , +≔ʳ)
∙-computeˡ ℓᵢ ℓₒ = no λ ()
∙-computeˡ ℓᵢ ℓ# = no λ ()
∙-computeˡ ℓₒ ℓ∅ = yes (ℓₒ , -≔ˡ)
∙-computeˡ ℓₒ ℓᵢ = no λ ()
∙-computeˡ ℓₒ ℓₒ = yes (ℓ∅ , -≔ʳ)
∙-computeˡ ℓₒ ℓ# = no λ ()
∙-computeˡ ℓ# ℓ∅ = yes (ℓ# , 1≔ˡ)
∙-computeˡ ℓ# ℓᵢ = yes (ℓₒ , splitʳ)
∙-computeˡ ℓ# ℓₒ = yes (ℓᵢ , splitˡ)
∙-computeˡ ℓ# ℓ# = yes (ℓ∅ , 1≔ʳ)

∙-unique : ∀ {x' x y z} → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
∙-unique 0≔ 0≔ = refl
∙-unique 1≔ˡ 1≔ˡ = refl
∙-unique 1≔ʳ 1≔ʳ = refl
∙-unique +≔ˡ +≔ˡ = refl
∙-unique +≔ʳ +≔ʳ = refl
∙-unique -≔ˡ -≔ˡ = refl
∙-unique -≔ʳ -≔ʳ = refl
∙-unique splitˡ splitˡ = refl
∙-unique splitʳ splitʳ = refl

∙-uniqueˡ : ∀ {x y' y z} → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y
∙-uniqueˡ 0≔ 0≔ = refl
∙-uniqueˡ 1≔ˡ 1≔ˡ = refl
∙-uniqueˡ 1≔ʳ 1≔ʳ = refl
∙-uniqueˡ +≔ˡ +≔ˡ = refl
∙-uniqueˡ +≔ʳ +≔ʳ = refl
∙-uniqueˡ -≔ˡ -≔ˡ = refl
∙-uniqueˡ -≔ʳ -≔ʳ = refl
∙-uniqueˡ splitˡ splitˡ = refl
∙-uniqueˡ splitʳ splitʳ = refl

∙-idˡ : ∀ x → x ≔ ℓ∅ ∙ x
∙-idˡ ℓ∅ = 0≔
∙-idˡ ℓᵢ = +≔ʳ
∙-idˡ ℓₒ = -≔ʳ
∙-idˡ ℓ# = 1≔ʳ

∙-comm : ∀ {x y z} → x ≔ y ∙ z → x ≔ z ∙ y
∙-comm 0≔ = 0≔
∙-comm 1≔ˡ = 1≔ʳ
∙-comm 1≔ʳ = 1≔ˡ
∙-comm +≔ˡ = +≔ʳ
∙-comm +≔ʳ = +≔ˡ
∙-comm -≔ˡ = -≔ʳ
∙-comm -≔ʳ = -≔ˡ
∙-comm splitˡ = splitʳ
∙-comm splitʳ = splitˡ

∙-assoc : ∀ {x y z u v} → x ≔ y ∙ z → y ≔ u ∙ v → ∃-syntax (λ ∝ → (x ≔ u ∙ w) × (w ≔ v ∙ z))
∙-assoc 0≔ 0≔ = ℓ∅ , 0≔ , 0≔
∙-assoc 1≔ˡ 1≔ˡ = ℓ∅ , 1≔ˡ , 0≔
∙-assoc 1≔ˡ 1≔ʳ = ℓ# , 1≔ʳ , 1≔ˡ
∙-assoc 1≔ˡ splitˡ = ℓₒ , splitˡ , -≔ˡ
∙-assoc 1≔ˡ splitʳ = ℓᵢ , splitʳ , +≔ˡ
∙-assoc 1≔ʳ 0≔ = ℓ# , 1≔ʳ , 1≔ʳ
∙-assoc +≔ˡ +≔ˡ = ℓ∅ , +≔ˡ , 0≔
∙-assoc +≔ˡ +≔ʳ = ℓᵢ , +≔ʳ , +≔ˡ
∙-assoc +≔ʳ 0≔ = ℓᵢ , +≔ʳ , +≔ʳ
∙-assoc -≔ˡ -≔ˡ = ℓ∅ , -≔ˡ , 0≔
∙-assoc -≔ˡ -≔ʳ = ℓₒ , -≔ʳ , -≔ˡ
∙-assoc -≔ʳ 0≔ = ℓₒ , -≔ʳ , -≔ʳ
∙-assoc splitˡ +≔ˡ = ℓₒ , splitˡ , -≔ʳ
∙-assoc splitˡ +≔ʳ = ℓ# , 1≔ʳ , splitˡ
∙-assoc splitʳ -≔ˡ = ℓᵢ , splitʳ , +≔ʳ
∙-assoc splitʳ -≔ʳ = ℓ# , 1≔ʳ , splitʳ

∙-join : ∀ {x y z} → x ≔ y ∙ ℓᵢ → x ≔ z ∙ ℓₒ → ∃-syntax (λ ∝ → x ≔ ∝ ∙ ℓ#)
∙-join splitʳ splitˡ = _ , 1≔ʳ

Linear : Quantifier Mult
Quantifier.ℓ∅ Linear = ℓ∅
Quantifier.ℓᵢ Linear = ℓᵢ
Quantifier.ℓₒ Linear = ℓₒ
Quantifier.ℓ# Linear = ℓ#
Quantifier._≔_∙_ Linear = _≔_∙_
Quantifier.∙-join Linear = ∙-join
Quantifier.∙-compute Linear = ∙-compute
Quantifier.∙-computeˡ Linear = ∙-computeˡ
Quantifier.∙-unique Linear = ∙-unique
Quantifier.∙-uniqueˡ Linear = ∙-uniqueˡ
Quantifier.∙-idˡ Linear = ∙-idˡ
Quantifier.∙-comm Linear = ∙-comm
Quantifier.∙-assoc Linear = ∙-assoc
