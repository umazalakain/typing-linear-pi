open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)

import Data.Product as Product
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open Product using (∃-syntax; _×_; _,_)
open ℕ using (ℕ)

open import PiCalculus.Quantifiers

module PiCalculus.LinearTypeSystem.LNL where

data Type : Set where
  nonlin lin : Type

data Mult : Type → Set where
  0∙ 1∙ : Mult lin
  ω∙ : Mult nonlin

ω0 : ∀ {i} → Mult i
ω0 {lin} = 0∙
ω0 {nonlin} = ω∙

ω1 : ∀ {i} → Mult i
ω1 {lin} = 1∙
ω1 {nonlin} = ω∙

data _≔_∙_ : ∀ {i} → Mult i → Mult i → Mult i → Set where
  share : ω∙ ≔ ω∙ ∙ ω∙
  left  : 1∙ ≔ 1∙ ∙ 0∙
  right : 1∙ ≔ 0∙ ∙ 1∙
  skip  : 0∙ ≔ 0∙ ∙ 0∙

∙-compute : ∀ {i} (y z : Mult i) → Dec (∃[ x ] (x ≔ y ∙ z))
∙-compute 0∙ 0∙ = yes (0∙ , skip)
∙-compute 0∙ 1∙ = yes (1∙ , right)
∙-compute 1∙ 0∙ = yes (1∙ , left)
∙-compute 1∙ 1∙ = no λ ()
∙-compute ω∙ ω∙ = yes (ω∙ , share)

∙-idˡ : ∀ {i} (x : Mult i) → x ≔ ω0 ∙ x
∙-idˡ 0∙ = skip
∙-idˡ 1∙ = right
∙-idˡ ω∙ = share

∙-unique : ∀ {i} {x x' y z : Mult i} → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
∙-unique share share = refl
∙-unique left left = refl
∙-unique right right = refl
∙-unique skip skip = refl

∙-cancelˡ : ∀ {i} {x y y' z : Mult i} → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y
∙-cancelˡ share share = refl
∙-cancelˡ left left = refl
∙-cancelˡ right right = refl
∙-cancelˡ skip skip = refl

∙-comm : ∀ {i} {x y z : Mult i} → x ≔ y ∙ z → x ≔ z ∙ y
∙-comm share = share
∙-comm left = right
∙-comm right = left
∙-comm skip = skip

∙-assoc : ∀ {i} {x y z u v : Mult i} → x ≔ y ∙ z → y ≔ u ∙ v
        → ∃[ w ] (x ≔ u ∙ w × w ≔ v ∙ z)
∙-assoc share share = ω∙ , share , share
∙-assoc left left = 0∙ , left , skip
∙-assoc left right = 1∙ , right , left
∙-assoc right skip = 1∙ , right , right
∙-assoc skip skip = 0∙ , skip , skip

LNL : Quantifiers
Quantifiers.I LNL = Type
Quantifiers.∃I LNL = nonlin
Quantifiers.C LNL = Mult
Quantifiers.0∙ LNL = ω0
Quantifiers.1∙ LNL = ω1
Quantifiers._≔_∙_ LNL = _≔_∙_
Quantifiers.∙-compute LNL = ∙-compute
Quantifiers.∙-idˡ LNL = ∙-idˡ
Quantifiers.∙-unique LNL = ∙-unique
Quantifiers.∙-cancelˡ LNL = ∙-cancelˡ
Quantifiers.∙-comm LNL = ∙-comm
Quantifiers.∙-assoc LNL = ∙-assoc
