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

open import PiCalculus.LinearTypeSystem.Algebras

module PiCalculus.LinearTypeSystem.Algebras.Linear where

open Bool using (Bool; true; false) public
pattern zero = false
pattern one = true

data _≔_∙_ : Bool → Bool → Bool → Set where
  skip  : zero ≔ zero ∙ zero
  right : one  ≔ zero ∙ one
  left  : one  ≔ one  ∙ zero

∙-computeʳ : ∀ x y → Dec (∃[ z ] (x ≔ y ∙ z))
∙-computeʳ zero zero = yes (zero , skip)
∙-computeʳ zero one = no λ ()
∙-computeʳ one zero = yes (one , right)
∙-computeʳ one one = yes (zero , left)

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

Linear : Algebra Bool
Algebra.1∙ Linear = true
Algebra.0∙ Linear = false
Algebra._≔_∙_ Linear = _≔_∙_
Algebra.∙-computeʳ Linear = ∙-computeʳ
Algebra.∙-unique Linear = ∙-unique
Algebra.∙-uniqueˡ Linear = ∙-uniqueˡ
Algebra.0∙-minˡ Linear skip = refl
Algebra.∙-idˡ Linear = ∙-idˡ
Algebra.∙-comm Linear = ∙-comm
Algebra.∙-assoc Linear = ∙-assoc
