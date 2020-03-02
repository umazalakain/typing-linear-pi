open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (fromWitness; toWitness)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim)

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

record Quantifier (Q : Set) : Set₁ where
  field
    0∙         : Q
    1∙         : Q
    _≔_∙_      : Q → Q → Q → Set

    -- Given two operands, we can decide whether a third one exists
    ∙-compute  : ∀ y z         → Dec (∃[ x ] (x ≔ y ∙ z))
    ∙-computeˡ : ∀ x z         → Dec (∃[ y ] (x ≔ y ∙ z))

    -- If a third operand exists, it must be unique
    ∙-unique   : ∀ {x x' y z}  → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
    ∙-uniqueˡ  : ∀ {x y y' z}  → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y

    ∙-idˡ      : ∀ x           → x ≔ 0∙ ∙ x
    ∙-comm     : ∀ {x y z}     → x ≔ y ∙ z → x ≔ z ∙ y -- no need for right rules
    ∙-assoc    : ∀ {x y z u v} → x ≔ y ∙ z → y ≔ u ∙ v → ∃[ w ] (x ≔ u ∙ w × w ≔ v ∙ z)

  ∙-idʳ : ∀ x → x ≔ x ∙ 0∙
  ∙-idʳ x = ∙-comm (∙-idˡ x)

record Quantifiers : Set₁ where
  field
    I  : Set
    ∃I : I
    Cs : I → Set
    Qs : ∀ i → Quantifier (Cs i)

  infixl 40 _-,_
  pattern _-,_ xs x = _∷_ x xs

  module _ {i : I} where
    A = Cs i
    open Quantifier (Qs i) public

    _≔_∙ᵥ_ : Vec A n → Vec A n → Vec A n → Set
    [] ≔ [] ∙ᵥ [] = ⊤
    xs -, x ≔ ys -, y ∙ᵥ zs -, z = xs ≔ ys ∙ᵥ zs × (x ≔ y ∙ z)

    ∙ᵥ-compute : (ys zs : Vec A n) → Dec (∃[ xs ] (xs ≔ ys ∙ᵥ zs))
    ∙ᵥ-compute [] [] = yes ([] , tt)
    ∙ᵥ-compute (ys -, y) (zs -, z) with ∙ᵥ-compute ys zs | ∙-compute y z
    ... | yes (_ , ps) | yes (_ , p) = yes ((_ -, _) , (ps , p))
    ... | yes (_ , ps) | no ¬p       = no λ {((_ -, _) , (_ , p)) → ¬p (_ , p)}
    ... | no ¬ps       | _           = no λ {((_ -, _) , (ps , _)) → ¬ps (_ , ps)}

    ∙ᵥ-computeˡ : (xs zs : Vec A n) → Dec (∃[ ys ] (xs ≔ ys ∙ᵥ zs))
    ∙ᵥ-computeˡ [] [] = yes ([] , tt)
    ∙ᵥ-computeˡ (xs -, x) (zs -, z) with ∙ᵥ-computeˡ xs zs | ∙-computeˡ x z
    ... | yes (_ , ps) | yes (_ , p) = yes ((_ -, _) , (ps , p))
    ... | yes (_ , ps) | no ¬p       = no λ {((_ -, _) , (_ , p)) → ¬p (_ , p)}
    ... | no ¬ps       | _           = no λ {((_ -, _) , (ps , _)) → ¬ps (_ , ps)}

    ∙ᵥ-idˡ : (xs : Vec A n) → xs ≔ Vec.replicate 0∙ ∙ᵥ xs
    ∙ᵥ-idˡ [] = tt
    ∙ᵥ-idˡ (xs -, x) = ∙ᵥ-idˡ xs , ∙-idˡ x

    ∙ᵥ-unique : {xs xs' ys zs : Vec A n} → xs' ≔ ys ∙ᵥ zs → xs ≔ ys ∙ᵥ zs → xs' ≡ xs
    ∙ᵥ-unique {xs = []} {[]} {[]} {[]} tt tt = refl
    ∙ᵥ-unique {xs = _ -, _} {_ -, _} {_ -, _} {_ -, _} (ps , p) (qs , q)
      rewrite ∙ᵥ-unique ps qs | ∙-unique p q = refl

    ∙ᵥ-uniqueˡ : {xs ys ys' zs : Vec A n} → xs ≔ ys' ∙ᵥ zs → xs ≔ ys ∙ᵥ zs → ys' ≡ ys
    ∙ᵥ-uniqueˡ {xs = []} {[]} {[]} {[]} tt tt = refl
    ∙ᵥ-uniqueˡ {xs = _ -, _} {_ -, _} {_ -, _} {_ -, _} (ps , p) (qs , q)
      rewrite ∙ᵥ-uniqueˡ ps qs | ∙-uniqueˡ p q = refl

    ∙ᵥ-comm : {xs ys zs : Vec A n} → xs ≔ ys ∙ᵥ zs → xs ≔ zs ∙ᵥ ys
    ∙ᵥ-comm {xs = []} {[]} {[]} tt = tt
    ∙ᵥ-comm {xs = _ -, _} {_ -, _} {_ -, _} (ps , p) = ∙ᵥ-comm ps , ∙-comm p

    ∙ᵥ-assoc : {m l r ll lr : Vec A n} → m ≔ l ∙ᵥ r → l ≔ ll ∙ᵥ lr → ∃[ r' ] (m ≔ ll ∙ᵥ r' × r' ≔ lr ∙ᵥ r)
    ∙ᵥ-assoc {m = []} {[]} {[]} {[]} {[]} tt tt = [] , tt , tt
    ∙ᵥ-assoc {m = _ -, _} {_ -, _} {_ -, _} {_ -, _} {_ -, _} (ms , m) (ls , l) with ∙ᵥ-assoc ms ls | ∙-assoc m l
    ... | (_ , ms' , rs') | (_ , m' , r') = _ , ((ms' , m') , (rs' , r'))

    ∙ᵥ-idʳ : (xs : Vec A n) → xs ≔ xs ∙ᵥ Vec.replicate 0∙
    ∙ᵥ-idʳ xs = ∙ᵥ-comm (∙ᵥ-idˡ xs)

    ∙ᵥ-compute-unique : ∀ {xs ys zs : Vec A n} (p : xs ≔ ys ∙ᵥ zs) → xs ≡ proj₁ (toWitness (fromWitness {Q = ∙ᵥ-compute _ _} (_ , p)))
    ∙ᵥ-compute-unique {ys = ys} {zs} p with ∙ᵥ-compute ys zs
    ∙ᵥ-compute-unique {ys = ys} {zs} p | yes (xs' , p') = ∙ᵥ-unique p p'
    ∙ᵥ-compute-unique {ys = ys} {zs} p | no ¬q = ⊥-elim (¬q (_ , p))
