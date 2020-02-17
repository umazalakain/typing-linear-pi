open import Relation.Binary.PropositionalEquality
open import Level using (Level)

module PiCalculus.Function where

infixl 9 _&_
infixl 8 _⊗_

private
  variable
    ℓ : Level
    A B : Set ℓ

_&_ : {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
f & refl = refl

_⊗_ : {f g : A → B} {x y : A} → f ≡ g → x ≡ y → f x ≡ g y
refl ⊗ refl = refl
