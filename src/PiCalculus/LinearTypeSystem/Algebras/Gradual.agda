{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (yes)

import Data.Product as Product
import Data.Sum as Sum
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open Product using (_,_)
open Sum using (inj₁)
open ℕ using (ℕ; _+_; zero; suc)

open import PiCalculus.LinearTypeSystem.Algebras
module PiCalculus.LinearTypeSystem.Algebras.Gradual where

_≔_∙_ : ℕ → ℕ → ℕ → Set
x ≔ y ∙ z = x ≡ (y + z)

Gradual : Algebra ℕ
Algebra.0∙ Gradual = 0
Algebra.1∙ Gradual = 1
Algebra._≔_∙_ Gradual = _≔_∙_
Algebra.∙-compute Gradual y z = yes (y + z , refl)
Algebra.∙-unique Gradual refl refl = refl
Algebra.∙-uniqueˡ Gradual refl = ℕₚ.+-cancelʳ-≡ _ _
Algebra.0∙-minˡ Gradual {zero} {zero} refl = refl
Algebra.∙-idˡ Gradual = refl
Algebra.∙-comm Gradual {y = y} refl = ℕₚ.+-comm y _
Algebra.∙-assoc Gradual {z = z} {v = v} refl refl = v + z , (ℕₚ.+-assoc _ v z , refl)
