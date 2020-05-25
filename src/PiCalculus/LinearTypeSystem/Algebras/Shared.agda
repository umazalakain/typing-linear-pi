{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes)

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁)

open import PiCalculus.LinearTypeSystem.Algebras

module PiCalculus.LinearTypeSystem.Algebras.Shared where

pattern ω = tt

Shared : Algebra ⊤
Algebra.0∙ Shared = ω
Algebra.1∙ Shared = ω
Algebra._≔_∙_ Shared _ _ _ = ⊤
Algebra.∙-computeʳ Shared _ _ = yes (ω , tt)
Algebra.∙-unique Shared _ _ = refl
Algebra.∙-uniqueˡ Shared _ _ = refl
Algebra.0∙-minˡ Shared _ = refl
Algebra.∙-idˡ Shared = tt
Algebra.∙-comm Shared _ = tt
Algebra.∙-assoc Shared _ _ = ω , tt , tt
