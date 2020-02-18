open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
open ℕ using (ℕ)

open import PiCalculus.Quantifiers

module PiCalculus.LinearTypeSystem.LNL where

data MType : Set where
  nonlin lin : MType

data ωℕ : MType → Set where
  n∙ : ℕ → ωℕ lin
  ω∙ : ωℕ nonlin

private
  private
    variable
      n : ℕ
      M N : MType

  ω0 : ωℕ M
  ω0 {nonlin} = ω∙
  ω0 {lin} = n∙ 0

  ω1 : ωℕ M
  ω1 {nonlin} = ω∙
  ω1 {lin} = n∙ 1

  _+_ : ωℕ M → ωℕ M → ωℕ M
  n∙ x + n∙ y = n∙ (x ℕ.+ y)
  ω∙ + ω∙ = ω∙

  n-injective : ∀ {x y} → n∙ x ≡ n∙ y → x ≡ y
  n-injective refl = refl

  +-idˡ : ∀ x → ω0 {M} + x ≡ x
  +-idˡ {nonlin} ω∙ = refl
  +-idˡ {lin} (n∙ _) = refl

  +-idʳ : ∀ x → x + ω0 {M} ≡ x
  +-idʳ {nonlin} ω∙ = refl
  +-idʳ {lin} (n∙ x) rewrite ℕₚ.+-identityʳ x = refl

  +-comm : (x y : ωℕ M) → x + y ≡ y + x
  +-comm (n∙ x) (n∙ y) rewrite ℕₚ.+-comm x y = refl
  +-comm ω∙ ω∙ = refl

  +-assoc : (x y z : ωℕ M) → (x + y) + z ≡ x + (y + z)
  +-assoc (n∙ x) (n∙ y) (n∙ z) rewrite ℕₚ.+-assoc x y z = refl
  +-assoc ω∙ ω∙ ω∙ = refl

  +-cancelˡ-≡ : {x y z : ωℕ M} → x + y ≡ x + z → y ≡ z
  +-cancelˡ-≡ {x = n∙ x} {n∙ _} {n∙ _} eq rewrite ℕₚ.+-cancelˡ-≡ x (n-injective eq) = refl
  +-cancelˡ-≡ {x = ω∙} {ω∙} {ω∙} _ = refl

LNL : Quantifiers
Quantifiers.I LNL = MType
Quantifiers.∃I LNL = nonlin
Quantifiers.C LNL = ωℕ
Quantifiers.0∙ LNL = ω0
Quantifiers.1∙ LNL = ω1
Quantifiers._+_ LNL = _+_
Quantifiers.+-idˡ LNL = +-idˡ
Quantifiers.+-idʳ LNL = +-idʳ
Quantifiers.+-assoc LNL = +-assoc
Quantifiers.+-comm LNL = +-comm
Quantifiers.+-cancelˡ-≡ LNL = +-cancelˡ-≡
