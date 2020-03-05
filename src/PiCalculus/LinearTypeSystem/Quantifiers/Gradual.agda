open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (Dec; yes; no)

import Data.Unit as Unit
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open Unit using (⊤; tt)
open Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open ℕ using (ℕ; _+_; zero; suc)

open import PiCalculus.Function
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Quantifiers.Gradual where

RS : Set
RS = ℕ × ℕ

private
  variable
    x⁺ x⁻ y⁺ y⁻ z⁺ z⁻ : ℕ

data _≔_∙_ : RS → RS → RS → Set where
  split : (x⁺ + y⁺ , x⁻ + y⁻) ≔ (x⁺ , x⁻) ∙ (y⁺ , y⁻)

to-≡ : (x⁺ , x⁻) ≔ (y⁺ , y⁻) ∙ (z⁺ , z⁻) → ((x⁺ , x⁻) ≡ (y⁺ + z⁺ , y⁻ + z⁻))
to-≡ split = refl

∙-comm : ∀ {x} → x ≔ (y⁺ , y⁻) ∙ (z⁺ , z⁻) → x ≔ (z⁺ , z⁻) ∙ (y⁺ , y⁻)
∙-comm {y⁺ = y⁺} {y⁻} {z⁺} {z⁻} split rewrite ℕₚ.+-comm y⁺ z⁺ | ℕₚ.+-comm y⁻ z⁻ = split

∙-compute : ∀ y z → Dec (∃[ x ] (x ≔ y ∙ z))
∙-compute (y⁺ , y⁻) (z⁺ , z⁻) = yes (_ , split)

∙-computeˡ : ∀ x z → Dec (∃[ y ] (x ≔ y ∙ z))
∙-computeˡ (x⁺ , x⁻) (z⁺ , z⁻) with z⁺ ℕₚ.≤″? x⁺ | z⁻ ℕₚ.≤″? x⁻
∙-computeˡ (x⁺ , x⁻) (z⁺ , z⁻) | yes (ℕ.less-than-or-equal refl) | yes (ℕ.less-than-or-equal refl) = yes (_ , ∙-comm split)
∙-computeˡ (x⁺ , x⁻) (z⁺ , z⁻) | yes p | no ¬q = no λ {(_ , split) → ¬q (ℕ.less-than-or-equal (ℕₚ.+-comm z⁻ _))}
∙-computeˡ (x⁺ , x⁻) (z⁺ , z⁻) | no ¬p | _     = no λ {(_ , split) → ¬p (ℕ.less-than-or-equal (ℕₚ.+-comm z⁺ _))}

∙-unique : ∀ {x x' y z} → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
∙-unique split split = refl

∙-uniqueˡ : ∀ {x y' y z} → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y
∙-uniqueˡ a b = let ab = trans (sym (to-≡ b)) (to-≡ a) in
              sym (_,_ & ℕₚ.+-cancelʳ-≡ _ _ (cong proj₁ ab)
                       ⊗ ℕₚ.+-cancelʳ-≡ _ _ (cong proj₂ ab))

∙-assoc : ∀ {x y z⁺ z⁻ u⁺ u⁻ v⁺ v⁻} → x ≔ y ∙ (z⁺ , z⁻) → y ≔ (u⁺ , u⁻) ∙ (v⁺ , v⁻) → ∃[ w ] ((x ≔ (u⁺ , u⁻) ∙ w) × (w ≔ (v⁺ , v⁻) ∙ (z⁺ , z⁻)))
∙-assoc {z⁺ = z⁺} {z⁻} {u⁺} {u⁻} {v⁺} {v⁻} split split
  rewrite ℕₚ.+-assoc u⁺ v⁺ z⁺ | ℕₚ.+-assoc u⁻ v⁻ z⁻
  = _ , (split , split)

∙-join' : ∀ {x⁺ x⁻ y⁺ y⁻ z⁺ z⁻}
        →         (x⁺ , x⁻) ≔ (1 , 0) ∙ (y⁺ , y⁻)
        →         (x⁺ , x⁻) ≔ (0 , 1) ∙ (z⁺ , z⁻)
        → ∃[ w ] ((x⁺ , x⁻) ≔ (1 , 1) ∙ w)
∙-join' split split = _ , split

∙-join : ∀ {x⁺ x⁻ y⁺ y⁻ z⁺ z⁻}
       → (x⁺ , x⁻) ≔ (y⁺ , y⁻) ∙ (1 , 0)
       → (x⁺ , x⁻) ≔ (z⁺ , z⁻) ∙ (0 , 1)
       → ∃[ w ] ((x⁺ , x⁻) ≔ w ∙ (1 , 1))
∙-join a b = _ , ∙-comm (proj₂ (∙-join' (∙-comm a) (∙-comm b)))

Gradual : Quantifier RS
Quantifier.0∙ Gradual = (0 , 0)
Quantifier.+∙ Gradual = (1 , 0)
Quantifier.-∙ Gradual = (0 , 1)
Quantifier.1∙ Gradual = (1 , 1)
Quantifier._≔_∙_ Gradual = _≔_∙_
Quantifier.∙-join Gradual = ∙-join
Quantifier.∙-compute Gradual = ∙-compute
Quantifier.∙-computeˡ Gradual = ∙-computeˡ
Quantifier.∙-unique Gradual = ∙-unique
Quantifier.∙-uniqueˡ Gradual = ∙-uniqueˡ
Quantifier.∙-idˡ Gradual (_ , _) = split
Quantifier.∙-comm Gradual = ∙-comm
Quantifier.∙-assoc Gradual = ∙-assoc
