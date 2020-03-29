open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes)

import Data.Product as Product
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open Product using (_,_)
open ℕ using (ℕ; _+_; zero; suc)

open import PiCalculus.LinearTypeSystem.Quantifiers
module PiCalculus.LinearTypeSystem.Quantifiers.Gradual where

_≔_∙_ : ℕ → ℕ → ℕ → Set
x ≔ y ∙ z = x ≡ (y + z)

Gradual : Quantifier ℕ
Quantifier.0∙ Gradual = 0
Quantifier.1∙ Gradual = 1
Quantifier._≔_∙_ Gradual = _≔_∙_
Quantifier.∙-compute Gradual y z = yes (y + z , refl)
Quantifier.∙-unique Gradual refl refl = refl
Quantifier.∙-uniqueˡ Gradual refl = ℕₚ.+-cancelʳ-≡ _ _
Quantifier.∙-idˡ Gradual _ = refl
Quantifier.∙-comm Gradual {y = y} refl = ℕₚ.+-comm y _
Quantifier.∙-assoc Gradual {z = z} {v = v} refl refl = v + z , (ℕₚ.+-assoc _ v z , refl)
