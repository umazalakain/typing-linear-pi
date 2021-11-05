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

  ∙-idʳ : ∀ {x} → x ≔ x ∙ 0∙
  ∙-idʳ = ∙-comm ∙-idˡ

  ∙-assoc⁻¹ : ∀ {x y z u v} → x ≔ y ∙ z → z ≔ u ∙ v → ∃[ ； ] (x ≔ ； ∙ v × ； ≔ y ∙ u)
  ∙-assoc⁻¹ a b = let _ , a' , b' = ∙-assoc (∙-comm a) (∙-comm b) in _ , ∙-comm a' , ∙-comm b'

  ∙-mut-cancel : ∀ {x y y' z} → x ≔ y ∙ z → z ≔ y' ∙ x → x ≡ z
  ∙-mut-cancel x≔y∙z z≔y'∙x with ∙-assoc⁻¹ x≔y∙z z≔y'∙x
  ∙-mut-cancel x≔y∙z z≔y'∙x | e , x≔e∙x , e≔y∙y' rewrite ∙-uniqueˡ x≔e∙x ∙-idˡ | 0∙-minˡ e≔y∙y' = ∙-unique x≔y∙z ∙-idˡ


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
