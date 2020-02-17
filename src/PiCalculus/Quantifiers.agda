open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

import Data.Product as Product
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
import Data.Nat as ℕ

open ℕ using (ℕ)
open Product using (Σ-syntax; _,_)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)

module PiCalculus.Quantifiers where

private
  variable
    n : ℕ

record Quantifiers : Set₁ where
  field
    I   : Set
    C   : I → Set
    0∙  : ∀ {i} → C i
    1∙  : ∀ {i} → C i
    _+_ : ∀ {i} → C i → C i → C i
    +-idˡ : ∀ {i} (x : C i) → 0∙ + x ≡ x
    +-idʳ : ∀ {i} (x : C i) → x + 0∙ ≡ x
    +-assoc : ∀ {i} (x y z : C i) → (x + y) + z ≡ x + (y + z)
    +-comm : ∀ {i} (x y : C i) → x + y ≡ y + x
    +-cancelˡ-≡ : ∀ {i} {x y z : C i} → x + y ≡ x + z → y ≡ z

  private
    variable
      Is : Vec I n

  _≤_ : ∀ {i} → C i → C i → Set
  x ≤ y = Σ[ z ∈ _ ] x + z ≡ y

  ≤-+ʳ : ∀ {i} {x y : C i} (z : C i) → x ≤ y → x ≤ (y + z)
  ≤-+ʳ {x = x} z (δ , refl) = (δ + z) , sym (+-assoc _ _ _)

  replicate : {Is : Vec I n} → (∀ {i} → C i) → All C Is
  replicate {Is = []} f = []
  replicate {Is = I ∷ Is} f = f {I} ∷ replicate f

  _+ᵥ_ : All C Is → All C Is → All C Is
  [] +ᵥ [] = []
  (x ∷ xs) +ᵥ (y ∷ ys) = x + y ∷ xs +ᵥ ys

  +ᵥ-idˡ : (xs : All C Is) → replicate 0∙ +ᵥ xs ≡ xs
  +ᵥ-idˡ [] = refl
  +ᵥ-idˡ (x ∷ xs) rewrite +ᵥ-idˡ xs | +-idˡ x = refl

  +ᵥ-idʳ : (xs : All C Is) → xs +ᵥ replicate 0∙ ≡ xs
  +ᵥ-idʳ [] = refl
  +ᵥ-idʳ (x ∷ xs) rewrite +ᵥ-idʳ xs | +-idʳ x = refl

  +ᵥ-assoc : (xs ys zs : All C Is) → (xs +ᵥ ys) +ᵥ zs ≡ xs +ᵥ (ys +ᵥ zs)
  +ᵥ-assoc [] [] [] = refl
  +ᵥ-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite +ᵥ-assoc xs ys zs | +-assoc x y z = refl

  +ᵥ-comm : (xs ys : All C Is) → xs +ᵥ ys ≡ ys +ᵥ xs
  +ᵥ-comm [] [] = refl
  +ᵥ-comm (x ∷ xs) (y ∷ ys) rewrite +ᵥ-comm xs ys | +-comm x y = refl

  +ᵥ-cancelˡ-≡ : {xs ys zs : All C Is} → xs +ᵥ ys ≡ xs +ᵥ zs → ys ≡ zs
  +ᵥ-cancelˡ-≡ {xs = []} {[]} {[]} _ = refl
  +ᵥ-cancelˡ-≡ {xs = _ ∷ _} {_ ∷ _} {_ ∷ _} eq
    rewrite +-cancelˡ-≡ (cong All.head eq)
    | +ᵥ-cancelˡ-≡ (cong All.tail eq)
    = refl

  _≤ᵥ_ : All C Is → All C Is → Set
  xs ≤ᵥ ys = Σ[ zs ∈ _ ] xs +ᵥ zs ≡ ys

  ≤ᵥ-refl : (xs : All C Is) → xs ≤ᵥ xs
  ≤ᵥ-refl xs = replicate 0∙ , +ᵥ-idʳ _

  ≤ᵥ-+ᵥʳ : {xs ys : All C Is} (zs : All C Is) → xs ≤ᵥ ys → xs ≤ᵥ (ys +ᵥ zs)
  ≤ᵥ-+ᵥʳ zs (δ , refl) = (δ +ᵥ zs) , sym (+ᵥ-assoc _ _ _)
