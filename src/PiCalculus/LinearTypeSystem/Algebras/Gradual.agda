{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (Dec; yes; no)

import Data.Product as Product
import Data.Sum as Sum
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open Product using (∃-syntax; _,_)
open Sum using (inj₁)
open ℕ using (ℕ; _+_; zero; suc)

open import PiCalculus.LinearTypeSystem.Algebras
module PiCalculus.LinearTypeSystem.Algebras.Gradual where

_≔_∙_ : ℕ → ℕ → ℕ → Set
x ≔ y ∙ z = x ≡ (y + z)

computeʳ : (x y : ℕ) → Dec (∃[ z ] (x ≔ y ∙ z))
computeʳ x y with y ℕₚ.≤″? x
computeʳ x y | yes (ℕ.less-than-or-equal proof) = yes (_ , (sym proof))
computeʳ x y | no ¬p = no λ where
  (_ , p) → ¬p (ℕ.less-than-or-equal (sym p))


Gradual : Algebra ℕ
Algebra.0∙ Gradual = 0
Algebra.1∙ Gradual = 1
Algebra._≔_∙_ Gradual = _≔_∙_
Algebra.∙-computeʳ Gradual = computeʳ
Algebra.∙-unique Gradual refl refl = refl
Algebra.∙-uniqueˡ Gradual refl = ℕₚ.+-cancelʳ-≡ _ _
Algebra.0∙-minˡ Gradual {zero} {zero} refl = refl
Algebra.∙-idˡ Gradual = refl
Algebra.∙-comm Gradual {y = y} refl = ℕₚ.+-comm y _
Algebra.∙-assoc Gradual {z = z} {v = v} refl refl = v + z , (ℕₚ.+-assoc _ v z , refl)
