{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
import Data.Vec.Relation.Unary.All as All
import Data.Nat as ℕ
import Data.Product as Prod
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Bool as Bool
import Data.Bool.Properties as Boolₚ
open Fin using (Fin; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open ℕ using (ℕ; zero; suc; s≤s; z≤n)
open Bool using (T; Bool; true; false; _∧_)


module PiCalculus.Function where

module _ where
  infixl 9 _&_
  infixl 8 _⊗_

  private
    variable
      n : ℕ
      ℓ ℓ₁ ℓ₂ : Level
      A B C D E F : Set ℓ

  _&_ : {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
  f & refl = refl

  _⊗_ : {f g : A → B} {x y : A} → f ≡ g → x ≡ y → f x ≡ g y
  refl ⊗ refl = refl

module _ where

  andᵥ : ∀ {n} → Vec Bool n → Bool
  andᵥ = Vec.foldr (λ _ → Bool) Bool._∧_ true

  All→Vec : ∀ {a b} {A : Set a} {P : A → Set b} {n} {xs : Vec A n} → All P xs → Vec (Σ A P) n
  All→Vec [] = []
  All→Vec (px ∷ pxs) = (_ , px) ∷ All→Vec pxs

  T-∧ : ∀ {x y : Bool} → T x × T y → T (x ∧ y)
  T-∧ {true} {true} (tt , tt) = tt

  ∧-T : ∀ {x y : Bool} → T (x ∧ y) → T x × T y
  ∧-T {true} {true} tt = tt , tt

module _ {a : Level} {A : Set a} {P : A → Bool} {f : A → A → A} where
  andᵥ-map-zipWith : (∀ (x y) → T (P x) → T (P y) → T (P (f x y)))
                   → ∀ {n} (xs ys : Vec A n)
                   → T (andᵥ (Vec.map P xs))
                   → T (andᵥ (Vec.map P ys))
                   → T (andᵥ (Vec.map P (Vec.zipWith f xs ys)))
  andᵥ-map-zipWith f [] [] tt tt = tt
  andᵥ-map-zipWith f (x ∷ xs) (y ∷ ys) Px∷xs Py∷ys
    = let (Px , Pxs) = ∧-T Px∷xs in
      let (Py , Pys) = ∧-T Py∷ys in
      T-∧ (f x y Px Py , andᵥ-map-zipWith f xs ys Pxs Pys)

module _ where
  private
    variable
      n : ℕ
      ℓ : Level
      A : Set ℓ

  lookup-≡ : {xs ys : Vec A n}
           → (∀ i → Vec.lookup xs i ≡ Vec.lookup ys i)
           → xs ≡ ys
  lookup-≡ {xs = []} {[]} f = refl
  lookup-≡ {xs = x ∷ xs} {y ∷ ys} f = _∷_ & f zero ⊗ lookup-≡ λ i → f (suc i)

module _  {a b} {X : Set a} {R : X → Set b} where
  unpack : ∀ {n} → Vec (Σ X R) n → Σ (Vec X n) λ xs → All R xs
  unpack [] = [] , []
  unpack (x ∷ xs) with unpack xs
  unpack ((_ , p) ∷ xs) | _ , ps = _ , p ∷ ps

  All-remove : ∀ {n} {xs : Vec X (suc n)}
             → (i : Fin (suc n)) → All R xs → All R (Vec.remove xs i)
  All-remove zero (p ∷ ps) = ps
  All-remove (suc i) (p ∷ q ∷ ps) = p ∷ All-remove i (q ∷ ps)

  All-lookup : ∀ {n} {xs : Vec X n} (i : Fin n)
             → (ps : All R xs) → R (Vec.lookup xs i)
  All-lookup zero (px ∷ ps) = px
  All-lookup (suc i) (px ∷ ps) = All-lookup i ps

  All-update : ∀ {n} {x : X} {xs : Vec X n} (i : Fin n) (ps : All R xs) (p : R x)
             → All R (xs Vec.[ i ]≔ x)
  All-update zero (px ∷ ps) p = p ∷ ps
  All-update (suc i) (px ∷ ps) p = px ∷ All-update i ps p
