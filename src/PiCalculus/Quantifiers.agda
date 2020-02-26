open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)

import Data.Unit as Unit
import Data.Product as Product
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
import Data.Nat as ℕ

open Unit using (⊤; tt)
open ℕ using (ℕ)
open Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)

module PiCalculus.Quantifiers where

private
  variable
    n : ℕ

record Quantifiers : Set₁ where
  field
    I         : Set
    ∃I        : I
    C         : I → Set
    0∙        : ∀ {i} → C i
    1∙        : ∀ {i} → C i
    _≔_∙_     : ∀ {i} → C i → C i → C i → Set
    ∙-compute : ∀ {i} (y z       : C i) → Dec (∃[ x ] (x ≔ y ∙ z))
    ∙-idˡ     : ∀ {i} (x         : C i) → x ≔ 0∙ ∙ x
    ∙-unique  : ∀ {i} {x x' y z  : C i} → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
    ∙-cancelˡ : ∀ {i} {x y y' z  : C i} → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y
    ∙-comm    : ∀ {i} {x y z     : C i} → x ≔ y ∙ z → x ≔ z ∙ y
    ∙-assoc   : ∀ {i} {x y z u v : C i} → x ≔ y ∙ z → y ≔ u ∙ v → ∃[ w ] (x ≔ u ∙ w × w ≔ v ∙ z)

  ∙-idʳ : ∀ {i} (x : C i) → x ≔ x ∙ 0∙
  ∙-idʳ x = ∙-comm (∙-idˡ x)

  private
    variable
      Is : Vec I n

  replicate : {Is : Vec I n} → (∀ {i} → C i) → All C Is
  replicate {Is = []} f = []
  replicate {Is = I ∷ Is} f = f {I} ∷ replicate f

  infix 50 _-,_
  pattern _-,_ xs x = _∷_ x xs

  _≔_∙ᵥ_ : All C Is → All C Is → All C Is → Set
  [] ≔ [] ∙ᵥ [] = ⊤
  xs -, x ≔ ys -, y ∙ᵥ zs -, z = xs ≔ ys ∙ᵥ zs × x ≔ y ∙ z

  ∙ᵥ-compute : (ys zs : All C Is) → Dec (∃[ xs ] (xs ≔ ys ∙ᵥ zs))
  ∙ᵥ-compute [] [] = yes ([] , tt)
  ∙ᵥ-compute (ys -, y) (zs -, z) with ∙ᵥ-compute ys zs | ∙-compute y z
  ... | yes (_ , ps) | yes (_ , p) = yes ((_ -, _) , (ps , p))
  ... | yes (_ , ps) | no ¬p       = no λ {((_ -, _) , (_ , p)) → ¬p (_ , p)}
  ... | no ¬ps       | _           = no λ {((_ -, _) , (ps , _)) → ¬ps (_ , ps)}

  ∙ᵥ-idˡ : (xs : All C Is) → xs ≔ replicate 0∙ ∙ᵥ xs
  ∙ᵥ-idˡ [] = tt
  ∙ᵥ-idˡ (xs -, x) = ∙ᵥ-idˡ xs , ∙-idˡ x

  ∙ᵥ-unique : {xs xs' ys zs : All C Is} → xs' ≔ ys ∙ᵥ zs → xs ≔ ys ∙ᵥ zs → xs' ≡ xs
  ∙ᵥ-unique {xs = []} {[]} {[]} {[]} tt tt = refl
  ∙ᵥ-unique {xs = _ -, _} {_ -, _} {_ -, _} {_ -, _} (ps , p) (qs , q)
    rewrite ∙ᵥ-unique ps qs | ∙-unique p q = refl

  ∙ᵥ-cancelˡ : {xs ys ys' zs : All C Is} → xs ≔ ys' ∙ᵥ zs → xs ≔ ys ∙ᵥ zs → ys' ≡ ys
  ∙ᵥ-cancelˡ {xs = []} {[]} {[]} {[]} tt tt = refl
  ∙ᵥ-cancelˡ {xs = _ -, _} {_ -, _} {_ -, _} {_ -, _} (ps , p) (qs , q)
    rewrite ∙ᵥ-cancelˡ ps qs | ∙-cancelˡ p q = refl

  ∙ᵥ-comm : {xs ys zs : All C Is} → xs ≔ ys ∙ᵥ zs → xs ≔ zs ∙ᵥ ys
  ∙ᵥ-comm {xs = []} {[]} {[]} tt = tt
  ∙ᵥ-comm {xs = _ -, _} {_ -, _} {_ -, _} (ps , p) = ∙ᵥ-comm ps , ∙-comm p

  ∙ᵥ-assoc : {m l r ll lr : All C Is} → m ≔ l ∙ᵥ r → l ≔ ll ∙ᵥ lr → ∃[ r' ] (m ≔ ll ∙ᵥ r' × r' ≔ lr ∙ᵥ r)
  ∙ᵥ-assoc {m = []} {[]} {[]} {[]} {[]} tt tt = [] , tt , tt
  ∙ᵥ-assoc {m = _ -, _} {_ -, _} {_ -, _} {_ -, _} {_ -, _} (ms , m) (ls , l) with ∙ᵥ-assoc ms ls | ∙-assoc m l
  ... | (_ , ms' , rs') | (_ , m' , r') = _ , ((ms' , m') , (rs' , r'))

  ∙ᵥ-idʳ : (xs : All C Is) → xs ≔ xs ∙ᵥ replicate 0∙
  ∙ᵥ-idʳ xs = ∙ᵥ-comm (∙ᵥ-idˡ xs)
