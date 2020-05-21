{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)

import Data.Bool as Bool
import Data.Empty as Empty
import Data.Unit as Unit
import Data.Sum as Sum
import Data.Product as Product
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open Empty using (⊥)
open Unit using (⊤; tt)
open Sum using (inj₁; inj₂)
open Product using (∃-syntax; _×_; _,_)
open ℕ using (ℕ)

open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Quantifiers.Linear where

open Bool using (Bool; true; false) public
pattern zero = false
pattern one = true

data _≔_∙_ : Bool → Bool → Bool → Set where
  skip  : zero ≔ zero ∙ zero
  right : one  ≔ zero ∙ one
  left  : one  ≔ one  ∙ zero

∙-compute : ∀ y z → Dec (∃[ x ] (x ≔ y ∙ z))
∙-compute zero zero = yes (zero , skip)
∙-compute zero one = yes (one , right)
∙-compute one zero = yes (one , left)
∙-compute one one = no λ { (zero , ()) ; (one , ())}

∙-computeˡ : ∀ x z → Dec (∃[ y ] (x ≔ y ∙ z))
∙-computeˡ zero zero = yes (zero , skip)
∙-computeˡ zero one = no λ { (zero , ()) ; (one , ())}
∙-computeˡ one zero = yes (one , left)
∙-computeˡ one one = yes (zero , right)

∙-unique : ∀ {x' x y z} → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
∙-unique skip skip = refl
∙-unique right right = refl
∙-unique left left = refl

∙-uniqueˡ : ∀ {x y' y z} → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y
∙-uniqueˡ skip skip = refl
∙-uniqueˡ right right = refl
∙-uniqueˡ left left = refl

∙-idˡ : ∀ {x} → x ≔ zero ∙ x
∙-idˡ {zero} = skip
∙-idˡ {one} = right

∙-comm : ∀ {x y z} → x ≔ y ∙ z → x ≔ z ∙ y
∙-comm skip = skip
∙-comm right = left
∙-comm left = right

∙-assoc : ∀ {x y z u v} → x ≔ y ∙ z → y ≔ u ∙ v → ∃-syntax (λ w → (x ≔ u ∙ w) × (w ≔ v ∙ z))
∙-assoc skip skip = zero , skip , skip
∙-assoc right skip = one , right , right
∙-assoc left right = one , right , left
∙-assoc left left = zero , left , skip

Linear : Quantifier Bool
Quantifier.1∙ Linear = true
Quantifier.0∙ Linear = false
Quantifier._≔_∙_ Linear = _≔_∙_
Quantifier.∙-compute Linear = ∙-compute
Quantifier.∙-unique Linear = ∙-unique
Quantifier.∙-uniqueˡ Linear = ∙-uniqueˡ
Quantifier.0∙-minˡ Linear skip = refl
Quantifier.∙-idˡ Linear = ∙-idˡ
Quantifier.∙-comm Linear = ∙-comm
Quantifier.∙-assoc Linear = ∙-assoc
