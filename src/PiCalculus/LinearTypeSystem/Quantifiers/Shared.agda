open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes)

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)

open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Quantifiers.Shared where

record Ω : Set where
  constructor ω∙

Shared : Quantifier Ω
Quantifier.0∙ Shared = ω∙
Quantifier.+∙ Shared = ω∙
Quantifier.-∙ Shared = ω∙
Quantifier.1∙ Shared = ω∙
Quantifier._≔_∙_ Shared _ _ _ = ⊤
Quantifier.∙-join Shared _ _ = ω∙ , tt
Quantifier.∙-compute Shared _ _ = yes (ω∙ , tt)
Quantifier.∙-computeˡ Shared _ _ = yes (ω∙ , tt)
Quantifier.∙-unique Shared _ _ = refl
Quantifier.∙-uniqueˡ Shared _ _ = refl
Quantifier.∙-idˡ Shared _ = tt
Quantifier.∙-comm Shared _ = tt
Quantifier.∙-assoc Shared _ _ = ω∙ , tt , tt
