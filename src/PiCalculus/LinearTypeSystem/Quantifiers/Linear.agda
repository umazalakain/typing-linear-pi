open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)

import Data.Bool as Bool
import Data.Empty as Empty
import Data.Unit as Unit
import Data.Sum as Sum
import Data.Product as Product
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open Bool using (Bool; true; false)
open Empty using (⊥)
open Unit using (⊤; tt)
open Sum using (inj₁; inj₂)
open Product using (∃-syntax; _×_; _,_)
open ℕ using (ℕ)

open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Quantifiers.Linear where

pattern zero = false
pattern one = true

_≔_∙_ : Bool → Bool → Bool → Set
zero ≔ zero ∙ zero = ⊤
zero ≔ _    ∙ _    = ⊥
one  ≔ zero ∙ one  = ⊤
one  ≔ one  ∙ zero = ⊤
one  ≔ _    ∙ _    = ⊥

∙-compute : ∀ y z → Dec (∃[ x ] (x ≔ y ∙ z))
∙-compute zero zero = yes (zero , tt)
∙-compute zero one = yes (one , tt)
∙-compute one zero = yes (one , tt)
∙-compute one one = no λ { (zero , ()) ; (one , ())}

∙-computeˡ : ∀ x z → Dec (∃[ y ] (x ≔ y ∙ z))
∙-computeˡ zero zero = yes (zero , tt)
∙-computeˡ zero one = no λ { (zero , ()) ; (one , ())}
∙-computeˡ one zero = yes (one , tt)
∙-computeˡ one one = yes (zero , tt)

∙-unique : ∀ {x' x y z} → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
∙-unique {zero} {zero} {zero} {zero} tt tt = refl
∙-unique {one} {one} {zero} {one} tt tt = refl
∙-unique {one} {one} {one} {zero} tt tt = refl

∙-uniqueˡ : ∀ {x y' y z} → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y
∙-uniqueˡ {zero} {zero} {zero} {zero} tt tt = refl
∙-uniqueˡ {one} {zero} {zero} {one} tt tt = refl
∙-uniqueˡ {one} {one} {one} {zero} tt tt = refl

∙-idˡ : ∀ x → x ≔ zero ∙ x
∙-idˡ zero = tt
∙-idˡ one = tt

∙-comm : ∀ {x y z} → x ≔ y ∙ z → x ≔ z ∙ y
∙-comm {zero} {zero} {zero} tt = tt
∙-comm {one} {zero} {one} tt = tt
∙-comm {one} {one} {zero} tt = tt

∙-assoc : ∀ {x y z u v} → x ≔ y ∙ z → y ≔ u ∙ v → ∃-syntax (λ w → (x ≔ u ∙ w) × (w ≔ v ∙ z))
∙-assoc {zero} {zero} {zero} {zero} {zero} tt tt = zero , (tt , tt)
∙-assoc {one} {zero} {one} {zero} {zero} tt tt = one , (tt , tt)
∙-assoc {one} {one} {zero} {zero} {one} tt tt = one , (tt , tt)
∙-assoc {one} {one} {zero} {one} {zero} tt tt = zero , (tt , tt) 

Linear : Quantifier Bool
Quantifier.1∙ Linear = true
Quantifier.0∙ Linear = false
Quantifier._≔_∙_ Linear = _≔_∙_
Quantifier.∙-compute Linear = ∙-compute
Quantifier.∙-unique Linear = ∙-unique
Quantifier.∙-uniqueˡ Linear = ∙-uniqueˡ
Quantifier.0∙-unique Linear {zero} {zero} tt = inj₁ refl
Quantifier.∙-idˡ Linear = ∙-idˡ
Quantifier.∙-comm Linear = ∙-comm
Quantifier.∙-assoc Linear = ∙-assoc
