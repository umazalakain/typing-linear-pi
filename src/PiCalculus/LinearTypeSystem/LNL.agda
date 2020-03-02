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
  0∙ 1∙ : Mult lin
  ω∙ : Mult nonlin

data _≔_∙_ : Mult lin → Mult lin → Mult lin → Set where
  left  : 1∙ ≔ 1∙ ∙ 0∙
  right : 1∙ ≔ 0∙ ∙ 1∙
  skip  : 0∙ ≔ 0∙ ∙ 0∙

∙-compute : ∀ y z → Dec (∃[ x ] (x ≔ y ∙ z))
∙-compute 0∙ 0∙ = yes (0∙ , skip)
∙-compute 0∙ 1∙ = yes (1∙ , right)
∙-compute 1∙ 0∙ = yes (1∙ , left)
∙-compute 1∙ 1∙ = no λ ()

∙-computeˡ : ∀ x z → Dec (∃[ y ] (x ≔ y ∙ z))
∙-computeˡ 0∙ 0∙ = yes (0∙ , skip)
∙-computeˡ 0∙ 1∙ = no λ ()
∙-computeˡ 1∙ 0∙ = yes (1∙ , left)
∙-computeˡ 1∙ 1∙ = yes (0∙ , right)

∙-idˡ : ∀ x → x ≔ 0∙ ∙ x
∙-idˡ 0∙ = skip
∙-idˡ 1∙ = right

∙-unique : ∀ {x x' y z} → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
∙-unique left left = refl
∙-unique right right = refl
∙-unique skip skip = refl

∙-uniqueˡ : ∀ {x y y' z} → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y
∙-uniqueˡ left left = refl
∙-uniqueˡ right right = refl
∙-uniqueˡ skip skip = refl

∙-comm : ∀ {x y z} → x ≔ y ∙ z → x ≔ z ∙ y
∙-comm left = right
∙-comm right = left
∙-comm skip = skip

∙-assoc : ∀ {x y z u v} → x ≔ y ∙ z → y ≔ u ∙ v → ∃[ w ] (x ≔ u ∙ w × w ≔ v ∙ z)
∙-assoc left left = 0∙ , left , skip
∙-assoc left right = 1∙ , right , left
∙-assoc right skip = 1∙ , right , right
∙-assoc skip skip = 0∙ , skip , skip

LNL : Quantifiers
Quantifiers.I LNL = Type
Quantifiers.∃I LNL = nonlin
Quantifiers.Cs LNL = Mult
Quantifier.0∙ (Quantifiers.Qs LNL nonlin) = ω∙
Quantifier.1∙ (Quantifiers.Qs LNL nonlin) = ω∙
Quantifier._≔_∙_ (Quantifiers.Qs LNL nonlin) _ _ _ = ⊤
Quantifier.∙-compute (Quantifiers.Qs LNL nonlin) _ _ = yes (ω∙ , tt)
Quantifier.∙-computeˡ (Quantifiers.Qs LNL nonlin) _ _ = yes (ω∙ , tt)
Quantifier.∙-idˡ (Quantifiers.Qs LNL nonlin) _ = tt
Quantifier.∙-unique (Quantifiers.Qs LNL nonlin) {x = ω∙} {x' = ω∙} _ _ = refl
Quantifier.∙-uniqueˡ (Quantifiers.Qs LNL nonlin) {y = ω∙} {y' = ω∙} _ _ = refl
Quantifier.∙-comm (Quantifiers.Qs LNL nonlin) _ = tt
Quantifier.∙-assoc (Quantifiers.Qs LNL nonlin) _ _ = ω∙ , (_ , _)
Quantifier.0∙ (Quantifiers.Qs LNL lin) = 0∙
Quantifier.1∙ (Quantifiers.Qs LNL lin) = 1∙
Quantifier._≔_∙_ (Quantifiers.Qs LNL lin) = _≔_∙_
Quantifier.∙-compute (Quantifiers.Qs LNL lin) = ∙-compute
Quantifier.∙-computeˡ (Quantifiers.Qs LNL lin) = ∙-computeˡ
Quantifier.∙-idˡ (Quantifiers.Qs LNL lin) = ∙-idˡ
Quantifier.∙-unique (Quantifiers.Qs LNL lin) = ∙-unique
Quantifier.∙-uniqueˡ (Quantifiers.Qs LNL lin) = ∙-uniqueˡ
Quantifier.∙-comm (Quantifiers.Qs LNL lin) = ∙-comm
Quantifier.∙-assoc (Quantifiers.Qs LNL lin) = ∙-assoc
