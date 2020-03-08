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

record Quantifier (Q : Set) : Set₁ where
  field
    0∙         : Q
    +∙         : Q
    -∙         : Q
    _≔_∙_      : Q → Q → Q → Set

    -- FIXME: we might not need this
    1∙         : Q
    ∙-join     : ∀ {x y z} → x ≔ y ∙ +∙ → x ≔ z ∙ -∙ → ∃[ w ] (x ≔ w ∙ 1∙)

    -- Given two operands, we can decide whether a third one exists
    ∙-compute  : ∀ y z         → Dec (∃[ x ] (x ≔ y ∙ z))

    -- FIXME: we might not need this
    ∙-computeˡ : ∀ x z         → Dec (∃[ y ] (x ≔ y ∙ z))

    -- If a third operand exists, it must be unique
    ∙-unique   : ∀ {x x' y z}  → x' ≔ y ∙ z → x ≔ y ∙ z → x' ≡ x
    ∙-uniqueˡ  : ∀ {x y y' z}  → x ≔ y' ∙ z → x ≔ y ∙ z → y' ≡ y

    ∙-idˡ      : ∀ x           → x ≔ 0∙ ∙ x
    ∙-comm     : ∀ {x y z}     → x ≔ y ∙ z → x ≔ z ∙ y -- no need for right rules
    ∙-assoc    : ∀ {x y z u v} → x ≔ y ∙ z → y ≔ u ∙ v → ∃[ w ] (x ≔ u ∙ w × w ≔ v ∙ z)

  ∙-idʳ : ∀ x → x ≔ x ∙ 0∙
  ∙-idʳ x = ∙-comm (∙-idˡ x)

  ∙-compute-unique : ∀ {x y z} (p : x ≔ y ∙ z) → x ≡ proj₁ (toWitness (fromWitness {Q = ∙-compute _ _} (_ , p)))
  ∙-compute-unique {y = y} {z} p with ∙-compute y z
  ∙-compute-unique {y = y} {z} p | yes (x' , p') = ∙-unique p p'
  ∙-compute-unique {y = y} {z} p | no ¬q = ⊥-elim (¬q (_ , p))

record Quantifiers : Set₁ where
  field
    I  : Set
    ∃I : I
    Cs : I → Set
    Qs : ∀ i → Quantifier (Cs i)

  infixl 40 _-,_
  pattern _-,_ xs x = _∷_ x xs

  module _ {i : I} where
    open Quantifier (Qs i) public

  private
    Ctx : Vec I n → Set
    Ctx = All Cs

    variable
      i : I
      is : Vec I n

  cast : {i j : I} → i ≡ j → Cs i → Cs j
  cast refl x = x

  _≔_⊎_ : Ctx is → Ctx is → Ctx is → Set
  _≔_⊎_ [] [] [] = ⊤
  _≔_⊎_ (Γ -, x) (Δ -, y) (Ξ -, z) = Γ ≔ Δ ⊎ Ξ × x ≔ y ∙ z

  ε : {is : Vec I n} → Ctx is
  ε {is = []} = []
  ε {is = _ -, _} = ε -, 0∙

  ⊎-get : {is : Vec I n} {Γ Δ Ξ : Ctx is} (i : Fin n) → Γ ≔ Δ ⊎ Ξ → All.lookup i Γ ≔ All.lookup i Δ ∙ All.lookup i Ξ
  ⊎-get {Γ = _ -, _} {_ -, _} {_ -, _} zero (Γ≔ , x≔) = x≔
  ⊎-get {Γ = _ -, _} {_ -, _} {_ -, _} (suc i) (Γ≔ , x≔) = ⊎-get i Γ≔

  ⊎-compute : (Δ Ξ : Ctx is) → Dec (∃[ Γ ] (Γ ≔ Δ ⊎ Ξ))
  ⊎-compute [] [] = yes ([] , tt)
  ⊎-compute (Δ -, y) (Ξ -, z) with ⊎-compute Δ Ξ | ∙-compute y z
  ... | yes (_ , ps)     | yes (_ , p) = yes ((_ -, _) , (ps , p))
  ... | yes (_ , ps)     | no ¬p       = no λ {((_ -, _) , (_ , p)) → ¬p (_ , p)}
  ... | no ¬ps           | _           = no λ {((_ -, _) , (ps , _)) → ¬ps (_ , ps)}

  ⊎-computeˡ : (Γ Ξ : Ctx is) → Dec (∃[ Δ ] (Γ ≔ Δ ⊎ Ξ))
  ⊎-computeˡ [] [] = yes ([] , tt)
  ⊎-computeˡ (Γ -, x) (Ξ -, z) with ⊎-computeˡ Γ Ξ | ∙-computeˡ x z
  ... | yes (_ , ps)     | yes (_ , p) = yes ((_ -, _) , (ps , p))
  ... | yes (_ , ps)     | no ¬p       = no λ {((_ -, _) , (_ , p)) → ¬p (_ , p)}
  ... | no ¬ps           | _           = no λ {((_ -, _) , (ps , _)) → ¬ps (_ , ps)}

  ⊎-idˡ : (Γ : Ctx is) → Γ ≔ ε ⊎ Γ
  ⊎-idˡ [] = tt
  ⊎-idˡ (Γ -, x) = ⊎-idˡ Γ , ∙-idˡ x

  ⊎-unique : {Γ Γ' Δ Ξ  : Ctx is} → Γ' ≔ Δ ⊎ Ξ → Γ ≔ Δ ⊎ Ξ → Γ' ≡ Γ
  ⊎-unique {Γ = []} {[]} {[]} {[]} tt tt = refl
  ⊎-unique {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} (Γ'≔ , x'≔) (Γ≔ , x≔)
    rewrite ⊎-unique Γ'≔ Γ≔ | ∙-unique x'≔ x≔ = refl

  ⊎-uniqueˡ : {Γ Δ Δ' Ξ  : Ctx is} → Γ ≔ Δ' ⊎ Ξ → Γ ≔ Δ ⊎ Ξ → Δ' ≡ Δ
  ⊎-uniqueˡ {Γ = []} {[]} {[]} {[]} tt tt = refl
  ⊎-uniqueˡ {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} (Δ'≔ , y'≔) (Δ≔ , y≔)
    rewrite ⊎-uniqueˡ Δ'≔ Δ≔ | ∙-uniqueˡ y'≔ y≔ = refl

  ⊎-comm : {Γ Δ Ξ : Ctx is} → Γ ≔ Δ ⊎ Ξ → Γ ≔ Ξ ⊎ Δ
  ⊎-comm {Γ = []} {[]} {[]} tt = tt
  ⊎-comm {Γ = _ -, _} {_ -, _} {_ -, _} (Γ≔ , x≔) = ⊎-comm Γ≔ , ∙-comm x≔

  ⊎-assoc : {Γₘ Γₗ Γᵣ Γₗₗ Γₗᵣ : Ctx is}
          → Γₘ ≔ Γₗ ⊎ Γᵣ → Γₗ ≔ Γₗₗ ⊎ Γₗᵣ → ∃[ Γᵣ' ] (Γₘ ≔ Γₗₗ ⊎ Γᵣ' × Γᵣ' ≔ Γₗᵣ ⊎ Γᵣ)
  ⊎-assoc {Γₘ = []} {[]} {[]} {[]} {[]}  tt tt = [] , tt , tt
  ⊎-assoc {Γₘ = _ -, _} {_ -, _} {_ -, _} {_ -, _} {_ -, _} (Γₘ≔ , xₘ≔) (Γₗ≔ , xₗ≔) with ⊎-assoc Γₘ≔ Γₗ≔ | ∙-assoc xₘ≔ xₗ≔
  ... | (_ , Γₘ'≔ , Γᵣ'≔)  | (_ , xₘ'≔ , xᵣ'≔) = _ , ((Γₘ'≔ , xₘ'≔) , (Γᵣ'≔ , xᵣ'≔))

  ⊎-trans : {m l r rl rr : Ctx is}
          → (t : m ≔ l ⊎ r) → (b : r ≔ rl ⊎ rr)
          → m ≔ proj₁ (⊎-assoc (⊎-comm t) (⊎-comm b)) ⊎ rr
  ⊎-trans t b = ⊎-comm (proj₁ (proj₂ (⊎-assoc (⊎-comm t) (⊎-comm b))))

  ⊎-comp : {Γ Δₗ Δᵣ Δ Ξ Θ : Ctx is}
         → Γ ≔ Δₗ ⊎ Ξ → Ξ ≔ Δᵣ ⊎ Θ
         → Γ ≔ Δ  ⊎ Θ → Δ ≔ Δₗ ⊎ Δᵣ
  ⊎-comp l≔ r≔ Γ≔ with ⊎-assoc (⊎-comm l≔) (⊎-comm r≔)
  ⊎-comp l≔ r≔ Γ≔ | _ , Γ'≔ , R'≔ rewrite ⊎-uniqueˡ Γ≔ (⊎-comm Γ'≔) = ⊎-comm R'≔

  ⊎-tail : {x y z : Ctx (is -, i)}
         → x ≔ y ⊎ z → All.tail x ≔ All.tail y ⊎ All.tail z
  ⊎-tail {x = _ -, _} {_ -, _} {_ -, _} (tail , _) = tail

  ⊎-idʳ : (Γ : Ctx is) → Γ ≔ Γ ⊎ ε
  ⊎-idʳ Γ = ⊎-comm (⊎-idˡ Γ)
