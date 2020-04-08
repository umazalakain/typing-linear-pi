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
open Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)

module PiCalculus.LinearTypeSystem.Quantifiers where

private
  variable
    n : ℕ


infixr 100 _²

_² : ∀ {a} → Set a → Set a
A ² = A × A

record Quantifier (Q : Set) : Set₁ where
  field
    0∙ 1∙       : Q

    _≔_∙_       : Q → Q → Q → Set

    -- Given two operands, we can decide whether a third one exists
    ∙-compute   : ∀ y z         → Dec (∃[ x ] (x ≔ y ∙ z))

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

  ∙-assoc⁻¹ : ∀ {x y z u v} → x ≔ y ∙ z → z ≔ u ∙ v → ∃[ ∝ ] (x ≔ ∝ ∙ v × ∝ ≔ y ∙ u)
  ∙-assoc⁻¹ a b = let _ , a' , b' = ∙-assoc (∙-comm a) (∙-comm b) in _ , ∙-comm a' , ∙-comm b'

  ∙-compute-unique : ∀ {x y z} (p : x ≔ y ∙ z) → x ≡ proj₁ (toWitness (fromWitness {Q = ∙-compute _ _} (_ , p)))
  ∙-compute-unique {y = y} {z} p with ∙-compute y z
  ∙-compute-unique {y = y} {z} p | yes (x' , p') = ∙-unique p p'
  ∙-compute-unique {y = y} {z} p | no ¬q = ⊥-elim (¬q (_ , p))

  ∙-mut-cancel : ∀ {x y y' z} → x ≔ y ∙ z → z ≔ y' ∙ x → x ≡ z
  ∙-mut-cancel x≔y∙z z≔y'∙x with ∙-assoc⁻¹ x≔y∙z z≔y'∙x
  ∙-mut-cancel x≔y∙z z≔y'∙x | e , x≔e∙x , e≔y∙y' rewrite ∙-uniqueˡ x≔e∙x ∙-idˡ | 0∙-minˡ e≔y∙y' = ∙-unique x≔y∙z ∙-idˡ

  ∙²-compute : ∀ y z → Dec (∃[ x ] (x ≔ y ∙² z))
  ∙²-compute (ly , ry) (lz , rz) with ∙-compute ly lz | ∙-compute ry rz
  ∙²-compute (ly , ry) (lz , rz) | yes (_ , p) | yes (_ , q) = yes (_ , (p , q))
  ∙²-compute (ly , ry) (lz , rz) | yes p | no ¬q = no λ {(_ , _ , r) → ¬q (_ , r)}
  ∙²-compute (ly , ry) (lz , rz) | no ¬p | _     = no λ {(_ , l , _) → ¬p (_ , l)}

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

  ∙²-compute-unique : ∀ {x y z} (p : x ≔ y ∙² z) → x ≡ proj₁ (toWitness (fromWitness {Q = ∙²-compute _ _} (_ , p)))
  ∙²-compute-unique {y = y} {z} p with ∙²-compute y z
  ∙²-compute-unique {y = y} {z} p | yes (x' , p') = ∙²-unique p p'
  ∙²-compute-unique {y = y} {z} p | no ¬q = ⊥-elim (¬q (_ , p))

  ∙²-mut-cancel : ∀ {x y y' z} → x ≔ y ∙² z → z ≔ y' ∙² x → x ≡ z
  ∙²-mut-cancel {_ , _} (lx , rx) (ly , ry) rewrite ∙-mut-cancel lx ly | ∙-mut-cancel rx ry = refl

record Quantifiers : Set₁ where
  field
    Idx     : Set
    ∃Idx   : Idx
    Carrier : Idx → Set
    Algebra : ∀ idx → Quantifier (Carrier idx)

  infixl 40 _-,_
  pattern _-,_ xs x = _∷_ x xs

  module _ {idx : Idx} where
    open Quantifier (Algebra idx) public

  Idxs : ℕ → Set
  Idxs = Vec Idx

  Ctx : ∀ {n} → Idxs n → Set
  Ctx = All λ idx → (Carrier idx) ²

  private
    variable
      idx : Idx
      idxs : Idxs n

  _≔_⊎_ : Ctx idxs → Ctx idxs → Ctx idxs → Set
  _≔_⊎_ [] [] [] = ⊤
  _≔_⊎_ (Γ -, x) (Δ -, y) (Ξ -, z) = Γ ≔ Δ ⊎ Ξ × x ≔ y ∙² z

  ε : ∀ {idxs : Idxs n} → Ctx idxs
  ε {idxs = []} = []
  ε {idxs = _ -, _} = ε -, (0∙ , 0∙)

  ⊎-get : {Γ Δ Ξ : Ctx idxs} (i : Fin n) → Γ ≔ Δ ⊎ Ξ → All.lookup i Γ ≔ All.lookup i Δ ∙² All.lookup i Ξ
  ⊎-get {Γ = _ -, _} {_ -, _} {_ -, _} zero (Γ≔ , x≔) = x≔
  ⊎-get {Γ = _ -, _} {_ -, _} {_ -, _} (suc i) (Γ≔ , x≔) = ⊎-get i Γ≔

  ⊎-compute : (Δ Ξ : Ctx idxs) → Dec (∃[ Γ ] (Γ ≔ Δ ⊎ Ξ))
  ⊎-compute [] [] = yes ([] , tt)
  ⊎-compute (Δ -, y) (Ξ -, z) with ⊎-compute Δ Ξ | ∙²-compute y z
  ... | yes (_ , ps)     | yes (_ , p) = yes ((_ -, _) , (ps , p))
  ... | yes (_ , ps)     | no ¬p       = no λ {((_ -, _) , (_ , p)) → ¬p (_ , p)}
  ... | no ¬ps           | _           = no λ {((_ -, _) , (ps , _)) → ¬ps (_ , ps)}

  ⊎-idˡ : {idxs : Idxs n} {Γ : Ctx idxs} → Γ ≔ ε ⊎ Γ
  ⊎-idˡ {Γ = []} = tt
  ⊎-idˡ {Γ = Γ -, x} = ⊎-idˡ , ∙²-idˡ

  ⊎-unique : {Γ Γ' Δ Ξ  : Ctx idxs} → Γ' ≔ Δ ⊎ Ξ → Γ ≔ Δ ⊎ Ξ → Γ' ≡ Γ
  ⊎-unique {Γ = []} {[]} {[]} {[]} tt tt = refl
  ⊎-unique {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} (Γ'≔ , x'≔) (Γ≔ , x≔)
    rewrite ⊎-unique Γ'≔ Γ≔ | ∙²-unique x'≔ x≔ = refl

  ⊎-uniqueˡ : {Γ Δ Δ' Ξ  : Ctx idxs} → Γ ≔ Δ' ⊎ Ξ → Γ ≔ Δ ⊎ Ξ → Δ' ≡ Δ
  ⊎-uniqueˡ {Γ = []} {[]} {[]} {[]} tt tt = refl
  ⊎-uniqueˡ {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} (Δ'≔ , y'≔) (Δ≔ , y≔)
    rewrite ⊎-uniqueˡ Δ'≔ Δ≔ | ∙²-uniqueˡ y'≔ y≔ = refl

  ⊎-comm : {Γ Δ Ξ : Ctx idxs} → Γ ≔ Δ ⊎ Ξ → Γ ≔ Ξ ⊎ Δ
  ⊎-comm {Γ = []} {[]} {[]} tt = tt
  ⊎-comm {Γ = _ -, _} {_ -, _} {_ -, _} (Γ≔ , x≔) = ⊎-comm Γ≔ , ∙²-comm x≔

  ⊎-assoc : {Γₘ Γₗ Γᵣ Γₗₗ Γₗᵣ : Ctx idxs}
          → Γₘ ≔ Γₗ ⊎ Γᵣ → Γₗ ≔ Γₗₗ ⊎ Γₗᵣ → ∃[ Γᵣ' ] (Γₘ ≔ Γₗₗ ⊎ Γᵣ' × Γᵣ' ≔ Γₗᵣ ⊎ Γᵣ)
  ⊎-assoc {Γₘ = []} {[]} {[]} {[]} {[]}  tt tt = [] , tt , tt
  ⊎-assoc {Γₘ = _ -, _} {_ -, _} {_ -, _} {_ -, _} {_ -, _} (Γₘ≔ , xₘ≔) (Γₗ≔ , xₗ≔) with ⊎-assoc Γₘ≔ Γₗ≔ | ∙²-assoc xₘ≔ xₗ≔
  ... | (_ , Γₘ'≔ , Γᵣ'≔)  | (_ , xₘ'≔ , xᵣ'≔) = _ , ((Γₘ'≔ , xₘ'≔) , (Γᵣ'≔ , xᵣ'≔))

  ⊎-trans : {m l r rl rr : Ctx idxs}
          → (t : m ≔ l ⊎ r) → (b : r ≔ rl ⊎ rr)
          → m ≔ proj₁ (⊎-assoc (⊎-comm t) (⊎-comm b)) ⊎ rr
  ⊎-trans t b = ⊎-comm (proj₁ (proj₂ (⊎-assoc (⊎-comm t) (⊎-comm b))))

  ⊎-comp : {Γ Δₗ Δᵣ Δ Ξ Θ : Ctx idxs}
         → Γ ≔ Δₗ ⊎ Ξ → Ξ ≔ Δᵣ ⊎ Θ
         → Γ ≔ Δ  ⊎ Θ → Δ ≔ Δₗ ⊎ Δᵣ
  ⊎-comp l≔ r≔ Γ≔ with ⊎-assoc (⊎-comm l≔) (⊎-comm r≔)
  ⊎-comp l≔ r≔ Γ≔ | _ , Γ'≔ , R'≔ rewrite ⊎-uniqueˡ Γ≔ (⊎-comm Γ'≔) = ⊎-comm R'≔

  ⊎-tail : {x y z : Ctx (idxs -, idx)}
         → x ≔ y ⊎ z → All.tail x ≔ All.tail y ⊎ All.tail z
  ⊎-tail {x = _ -, _} {_ -, _} {_ -, _} (tail , _) = tail

  ⊎-idʳ : (Γ : Ctx idxs) → Γ ≔ Γ ⊎ ε
  ⊎-idʳ Γ = ⊎-comm ⊎-idˡ

  ⊎-mut-cancel : ∀ {x y y' z : Ctx idxs} → x ≔ y ⊎ z → z ≔ y' ⊎ x → x ≡ z
  ⊎-mut-cancel {x = []} {[]} {[]} {[]} Γ Ξ = refl
  ⊎-mut-cancel {x = _ -, _} {_ -, _} {_ -, _} {_ -, _} (Γ≔ , x≔) (Ξ≔ , z≔)
    rewrite ⊎-mut-cancel Γ≔ Ξ≔
    | ∙²-mut-cancel x≔ z≔ = refl
