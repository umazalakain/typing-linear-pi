{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (fromWitness; toWitness)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim)

import Data.Fin as Fin
import Data.Unit as Unit
import Data.Product as Product
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
import Data.Nat as ℕ

open Fin using (Fin; zero; suc)
open Unit using (⊤; tt)
open ℕ using (ℕ)
open Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)

module PiCalculus.LinearTypeSystem.Algebras where

private
  variable
    n : ℕ


infixr 100 _²

_² : ∀ {a} → Set a → Set a
A ² = A × A

record Algebra (Q : Set) : Set₁ where
  field
    0∙ 1∙       : Q

    _≔_∙_       : Q → Q → Q → Set

    -- Given two operands, we can decide whether a third one exists
    ∙-computeʳ  : ∀ x y         → Dec (∃[ z ] (x ≔ y ∙ z))

    -- If a third operand exists, it must be unique
    ∙-unique    : ∀ {x x' y z}  → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
    ∙-uniqueˡ   : ∀ {x y y' z}  → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y

    -- 0 is the minimum
    0∙-minˡ     : ∀ {y z}       → 0∙ ≔ y ∙ z → y ≡ 0∙

    -- Neutral element, commutativity, associativity
    ∙-idˡ       : ∀ {x}         → x ≔ 0∙ ∙ x
    ∙-comm      : ∀ {x y z}     → x ≔ y ∙ z → x ≔ z ∙ y -- no need for right rules
    ∙-assoc     : ∀ {x y z u v} → x ≔ y ∙ z → y ≔ u ∙ v → ∃[ w ] (x ≔ u ∙ w × w ≔ v ∙ z)

  ℓ∅ : Q ²
  ℓ∅ = 0∙ , 0∙

  ℓᵢ : Q ²
  ℓᵢ = 1∙ , 0∙

  ℓₒ : Q ²
  ℓₒ = 0∙ , 1∙

  ℓ# : Q ²
  ℓ# = 1∙ , 1∙

  _≔_∙²_ : Q ² → Q ² → Q ² → Set
  (lx , rx) ≔ (ly , ry) ∙² (lz , rz) = (lx ≔ ly ∙ lz) × (rx ≔ ry ∙ rz)

  ∙-idʳ : ∀ {x} → x ≔ x ∙ 0∙
  ∙-idʳ = ∙-comm ∙-idˡ

  ∙-assoc⁻¹ : ∀ {x y z u v} → x ≔ y ∙ z → z ≔ u ∙ v → ∃[ ； ] (x ≔ ； ∙ v × ； ≔ y ∙ u)
  ∙-assoc⁻¹ a b = let _ , a' , b' = ∙-assoc (∙-comm a) (∙-comm b) in _ , ∙-comm a' , ∙-comm b'

  ∙-mut-cancel : ∀ {x y y' z} → x ≔ y ∙ z → z ≔ y' ∙ x → x ≡ z
  ∙-mut-cancel x≔y∙z z≔y'∙x with ∙-assoc⁻¹ x≔y∙z z≔y'∙x
  ∙-mut-cancel x≔y∙z z≔y'∙x | e , x≔e∙x , e≔y∙y' rewrite ∙-uniqueˡ x≔e∙x ∙-idˡ | 0∙-minˡ e≔y∙y' = ∙-unique x≔y∙z ∙-idˡ

  ∙²-computeʳ : ∀ x y → Dec (∃[ z ] (x ≔ y ∙² z))
  ∙²-computeʳ (lx , rx) (ly , ry) with ∙-computeʳ lx ly | ∙-computeʳ rx ry
  ∙²-computeʳ (lx , rx) (ly , ry) | yes (_ , p) | yes (_ , q) = yes (_ , p , q)
  ∙²-computeʳ (lx , rx) (ly , ry) | yes p | no ¬q = no λ {(_ , _ , r) → ¬q (_ , r)}
  ∙²-computeʳ (lx , rx) (ly , ry) | no ¬p | _     = no λ {(_ , l , _) → ¬p (_ , l)}

  ∙²-unique : ∀ {x x' y z} → x' ≔ y ∙² z → x ≔ y ∙² z → x' ≡ x
  ∙²-unique {x = _ , _} {x' = _ , _} (ll , rl) (lr , rr)
    rewrite ∙-unique ll lr | ∙-unique rl rr = refl

  ∙²-uniqueˡ : ∀ {x y y' z} → x ≔ y' ∙² z → x ≔ y ∙² z → y' ≡ y
  ∙²-uniqueˡ {y = _ , _} {y' = _ , _} (ll , lr) (rl , rr)
    rewrite ∙-uniqueˡ ll rl | ∙-uniqueˡ lr rr = refl

  ∙²-idˡ : ∀ {x} → x ≔ (0∙ , 0∙) ∙² x
  ∙²-idˡ = ∙-idˡ , ∙-idˡ

  ∙²-comm : ∀ {x y z} → x ≔ y ∙² z → x ≔ z ∙² y
  ∙²-comm (lx , rx) = ∙-comm lx , ∙-comm rx

  ∙²-idʳ : ∀ {x} → x ≔ x ∙² (0∙ , 0∙)
  ∙²-idʳ = ∙²-comm ∙²-idˡ

  ∙²-assoc : ∀ {x y z u v} → x ≔ y ∙² z → y ≔ u ∙² v → ∃[ w ] (x ≔ u ∙² w × w ≔ v ∙² z)
  ∙²-assoc (lx , rx) (ly , ry) with ∙-assoc lx ly | ∙-assoc rx ry
  ∙²-assoc (lx , rx) (ly , ry) | _ , ll , rl | _ , lr , rr = _ , ((ll , lr) , (rl , rr))

  ∙²-assoc⁻¹ : ∀ {x y z u v} → x ≔ y ∙² z → z ≔ u ∙² v → ∃[ ； ] (x ≔ ； ∙² v × ； ≔ y ∙² u)
  ∙²-assoc⁻¹ a b = let _ , a' , b' = ∙²-assoc (∙²-comm a) (∙²-comm b) in _ , ∙²-comm a' , ∙²-comm b'

  ∙²-mut-cancel : ∀ {x y y' z} → x ≔ y ∙² z → z ≔ y' ∙² x → x ≡ z
  ∙²-mut-cancel {_ , _} (lx , rx) (ly , ry) rewrite ∙-mut-cancel lx ly | ∙-mut-cancel rx ry = refl

record Algebras : Set₁ where
  field
    Idx          : Set
    ∃Idx         : Idx
    Usage        : Idx → Set
    UsageAlgebra : ∀ idx → Algebra (Usage idx)

  infixl 40 _-,_
  pattern _-,_ xs x = _∷_ x xs

  module _ {idx : Idx} where
    open Algebra (UsageAlgebra idx) public
