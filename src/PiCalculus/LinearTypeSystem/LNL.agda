open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)

import Data.Unit as Unit
import Data.Product as Product
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open Unit using (⊤; tt)
open Product using (∃-syntax; _×_; _,_)
open ℕ using (ℕ)

open import PiCalculus.Quantifiers

module PiCalculus.LinearTypeSystem.LNL where

data Type : Set where
  nonlin lin : Type

data Mult : Type → Set where
  ω∙          : Mult nonlin
  0∙ +∙ -∙ 1∙ : Mult lin

data _≔_∙_ : Mult lin → Mult lin → Mult lin → Set where
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

∙-assoc : ∀ {x y z u v} → x ≔ y ∙ z → y ≔ u ∙ v → ∃-syntax (λ w → (x ≔ u ∙ w) × (w ≔ v ∙ z))
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

LNL : Quantifiers
Quantifiers.I LNL = Type
Quantifiers.∃I LNL = nonlin
Quantifiers.Cs LNL = Mult
Quantifier.0∙ (Quantifiers.Qs LNL nonlin) = ω∙
Quantifier.+∙ (Quantifiers.Qs LNL nonlin) = ω∙
Quantifier.-∙ (Quantifiers.Qs LNL nonlin) = ω∙
Quantifier.1∙ (Quantifiers.Qs LNL nonlin) = ω∙
Quantifier._≔_∙_ (Quantifiers.Qs LNL nonlin) _ _ _ = ⊤
Quantifier.∙-split (Quantifiers.Qs LNL nonlin) = tt
Quantifier.∙-compute (Quantifiers.Qs LNL nonlin) _ _ = yes (ω∙ , tt)
Quantifier.∙-computeˡ (Quantifiers.Qs LNL nonlin) _ _ = yes (ω∙ , tt)
Quantifier.∙-unique (Quantifiers.Qs LNL nonlin) {x = ω∙} {x' = ω∙} _ _ = refl
Quantifier.∙-uniqueˡ (Quantifiers.Qs LNL nonlin) {y = ω∙} {y' = ω∙} _ _ = refl
Quantifier.∙-idˡ (Quantifiers.Qs LNL nonlin) _ = tt
Quantifier.∙-comm (Quantifiers.Qs LNL nonlin) _ = tt
Quantifier.∙-assoc (Quantifiers.Qs LNL nonlin) _ _ = ω∙ , (_ , _)
Quantifier.0∙ (Quantifiers.Qs LNL lin) = 0∙
Quantifier.+∙ (Quantifiers.Qs LNL lin) = +∙
Quantifier.-∙ (Quantifiers.Qs LNL lin) = -∙
Quantifier.1∙ (Quantifiers.Qs LNL lin) = 1∙
Quantifier._≔_∙_ (Quantifiers.Qs LNL lin) = _≔_∙_
Quantifier.∙-split (Quantifiers.Qs LNL lin) = splitˡ
Quantifier.∙-compute (Quantifiers.Qs LNL lin) = ∙-compute
Quantifier.∙-computeˡ (Quantifiers.Qs LNL lin) = ∙-computeˡ
Quantifier.∙-unique (Quantifiers.Qs LNL lin) = ∙-unique
Quantifier.∙-uniqueˡ (Quantifiers.Qs LNL lin) = ∙-uniqueˡ
Quantifier.∙-idˡ (Quantifiers.Qs LNL lin) = ∙-idˡ
Quantifier.∙-comm (Quantifiers.Qs LNL lin) = ∙-comm
Quantifier.∙-assoc (Quantifiers.Qs LNL lin) = ∙-assoc
