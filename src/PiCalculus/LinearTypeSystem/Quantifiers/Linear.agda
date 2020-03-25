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
  0∙ +∙ -∙ 1∙ : Mult

data _≔_∙_ : Mult → Mult → Mult → Set where
  0≔ : 0∙ ≔ 0∙ ∙ 0∙
  1≔ˡ : 1∙ ≔ 1∙ ∙ 0∙
  1≔ʳ : 1∙ ≔ 0∙ ∙ 1∙
  +≔ˡ : +∙ ≔ +∙ ∙ 0∙
  +≔ʳ : +∙ ≔ 0∙ ∙ +∙
  -≔ˡ : -∙ ≔ -∙ ∙ 0∙
  -≔ʳ : -∙ ≔ 0∙ ∙ -∙
  splitˡ : 1∙ ≔ +∙ ∙ -∙
  splitʳ : 1∙ ≔ -∙ ∙ +∙

∙-compute : ∀ y z → Dec (∃[ x ] (x ≔ y ∙ z))
∙-compute 0∙ 0∙ = yes (0∙ , 0≔)
∙-compute 0∙ +∙ = yes (+∙ , +≔ʳ)
∙-compute 0∙ -∙ = yes (-∙ , -≔ʳ)
∙-compute 0∙ 1∙ = yes (1∙ , 1≔ʳ)
∙-compute +∙ 0∙ = yes (+∙ , +≔ˡ)
∙-compute +∙ +∙ = no λ ()
∙-compute +∙ -∙ = yes (1∙ , splitˡ)
∙-compute +∙ 1∙ = no λ ()
∙-compute -∙ 0∙ = yes (-∙ , -≔ˡ)
∙-compute -∙ +∙ = yes (1∙ , splitʳ)
∙-compute -∙ -∙ = no λ ()
∙-compute -∙ 1∙ = no λ ()
∙-compute 1∙ 0∙ = yes (1∙ , 1≔ˡ)
∙-compute 1∙ +∙ = no λ ()
∙-compute 1∙ -∙ = no λ ()
∙-compute 1∙ 1∙ = no λ ()

∙-computeˡ : ∀ x z → Dec (∃[ y ] (x ≔ y ∙ z))
∙-computeˡ 0∙ 0∙ = yes (0∙ , 0≔)
∙-computeˡ 0∙ +∙ = no λ ()
∙-computeˡ 0∙ -∙ = no λ ()
∙-computeˡ 0∙ 1∙ = no λ ()
∙-computeˡ +∙ 0∙ = yes (+∙ , +≔ˡ)
∙-computeˡ +∙ +∙ = yes (0∙ , +≔ʳ)
∙-computeˡ +∙ -∙ = no λ ()
∙-computeˡ +∙ 1∙ = no λ ()
∙-computeˡ -∙ 0∙ = yes (-∙ , -≔ˡ)
∙-computeˡ -∙ +∙ = no λ ()
∙-computeˡ -∙ -∙ = yes (0∙ , -≔ʳ)
∙-computeˡ -∙ 1∙ = no λ ()
∙-computeˡ 1∙ 0∙ = yes (1∙ , 1≔ˡ)
∙-computeˡ 1∙ +∙ = yes (-∙ , splitʳ)
∙-computeˡ 1∙ -∙ = yes (+∙ , splitˡ)
∙-computeˡ 1∙ 1∙ = yes (0∙ , 1≔ʳ)

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

∙-idˡ : ∀ x → x ≔ 0∙ ∙ x
∙-idˡ 0∙ = 0≔
∙-idˡ +∙ = +≔ʳ
∙-idˡ -∙ = -≔ʳ
∙-idˡ 1∙ = 1≔ʳ

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
∙-assoc 0≔ 0≔ = 0∙ , 0≔ , 0≔
∙-assoc 1≔ˡ 1≔ˡ = 0∙ , 1≔ˡ , 0≔
∙-assoc 1≔ˡ 1≔ʳ = 1∙ , 1≔ʳ , 1≔ˡ
∙-assoc 1≔ˡ splitˡ = -∙ , splitˡ , -≔ˡ
∙-assoc 1≔ˡ splitʳ = +∙ , splitʳ , +≔ˡ
∙-assoc 1≔ʳ 0≔ = 1∙ , 1≔ʳ , 1≔ʳ
∙-assoc +≔ˡ +≔ˡ = 0∙ , +≔ˡ , 0≔
∙-assoc +≔ˡ +≔ʳ = +∙ , +≔ʳ , +≔ˡ
∙-assoc +≔ʳ 0≔ = +∙ , +≔ʳ , +≔ʳ
∙-assoc -≔ˡ -≔ˡ = 0∙ , -≔ˡ , 0≔
∙-assoc -≔ˡ -≔ʳ = -∙ , -≔ʳ , -≔ˡ
∙-assoc -≔ʳ 0≔ = -∙ , -≔ʳ , -≔ʳ
∙-assoc splitˡ +≔ˡ = -∙ , splitˡ , -≔ʳ
∙-assoc splitˡ +≔ʳ = 1∙ , 1≔ʳ , splitˡ
∙-assoc splitʳ -≔ˡ = +∙ , splitʳ , +≔ʳ
∙-assoc splitʳ -≔ʳ = 1∙ , 1≔ʳ , splitʳ

∙-join : ∀ {x y z} → x ≔ y ∙ +∙ → x ≔ z ∙ -∙ → ∃-syntax (λ ∝ → x ≔ ∝ ∙ 1∙)
∙-join splitʳ splitˡ = _ , 1≔ʳ

Linear : Quantifier Mult
Quantifier.0∙ Linear = 0∙
Quantifier.+∙ Linear = +∙
Quantifier.-∙ Linear = -∙
Quantifier.1∙ Linear = 1∙
Quantifier._≔_∙_ Linear = _≔_∙_
Quantifier.∙-join Linear = ∙-join
Quantifier.∙-compute Linear = ∙-compute
Quantifier.∙-computeˡ Linear = ∙-computeˡ
Quantifier.∙-unique Linear = ∙-unique
Quantifier.∙-uniqueˡ Linear = ∙-uniqueˡ
Quantifier.∙-idˡ Linear = ∙-idˡ
Quantifier.∙-comm Linear = ∙-comm
Quantifier.∙-assoc Linear = ∙-assoc
