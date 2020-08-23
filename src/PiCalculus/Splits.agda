{-# OPTIONS --safe --without-K #-}

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
import Data.Nat.Properties as ℕₚ

module PiCalculus.Splits where

private
  variable
    n m l k : ℕ
    x y : Fin n

data _+_≔_ : ℕ → ℕ → ℕ → Set where
  zero  :             zero  + zero  ≔ zero
  left  : n + m ≔ l → suc n + m     ≔ suc l
  right : n + m ≔ l → n     + suc m ≔ suc l

invert : n + m ≔ l → Fin l → Fin n ⊎ Fin m
invert (left ρ) zero = inj₁ zero
invert (right ρ) zero = inj₂ zero
invert (left ρ) (suc x) = Sum.map suc id (invert ρ x)
invert (right ρ) (suc x) = Sum.map id suc (invert ρ x)

+-identityʳ : n + zero ≔ n
+-identityʳ {zero} = zero
+-identityʳ {suc n} = left +-identityʳ

+-cancelˡ : zero + m ≔ l → m ≡ l
+-cancelˡ zero = refl
+-cancelˡ (right ρ) = cong suc (+-cancelˡ ρ)

+-comm : n + m ≔ l → m + n ≔ l
+-comm zero = zero
+-comm (left ρ) = right (+-comm ρ)
+-comm (right ρ) = left (+-comm ρ)

left-first : ∀ n m → m + n ≔ (n ℕ.+ m)
left-first zero zero = zero
left-first (suc n) m = right (left-first n m)
left-first zero (suc m) = left (left-first zero m)

left-first′ : ∀ n m → n + m ≔ (n ℕ.+ m)
left-first′ zero zero = zero
left-first′ zero (suc m) = right (left-first′ zero m)
left-first′ (suc n) m = left (left-first′ n m)

+-fromFin : Fin (suc n) → n + 1 ≔ suc n
+-fromFin zero = right +-identityʳ
+-fromFin {suc n} (suc i) = left (+-fromFin i)

+-toFin : n + 1 ≔ m → Fin m
+-toFin (left s) = suc (+-toFin s)
+-toFin (right s) = zero

extend : ∀ k → n + m ≔ l → (k ℕ.+ n) + m ≔ (k ℕ.+ l)
extend {n = n} {l = l} zero ρ = ρ
extend {n = n} {l = l} (suc k) ρ = left (extend k ρ)

module _ {a} {A : Set a} where
  open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

  vec-merge : (ρ : n + m ≔ l) → Vec A n → Vec A m → Vec A l
  vec-merge zero [] [] = []
  vec-merge (left ρ) (x ∷ xs) ys = x ∷ vec-merge ρ xs ys
  vec-merge (right ρ) xs (y ∷ ys) = y ∷ vec-merge ρ xs ys

  vec-merge-idˡ : ∀ (ρ : 0 + n ≔ n) xs → vec-merge ρ [] xs ≡ xs
  vec-merge-idˡ zero [] = refl
  vec-merge-idˡ (right ρ) (x ∷ xs) = cong (x ∷_) (vec-merge-idˡ ρ xs)

  vec-++ : Vec A n → Vec A m → Vec A (n ℕ.+ m)
  vec-++ xs ys = vec-merge (left-first′ _ _) xs ys

  vec-update : (ρ : n + 1 ≔ m) → A → Vec A m → Vec A m
  vec-update (left ρ) y (x ∷ xs) = x ∷ vec-update ρ y xs
  vec-update (right ρ) y (x ∷ xs) = y ∷ xs

  vec-split : (ρ : n + m ≔ l) → Vec A l → Vec A n × Vec A m
  vec-split zero [] = [] , []
  vec-split (left ρ) (x ∷ xs) = Product.map (x ∷_) id (vec-split ρ xs)
  vec-split (right ρ) (x ∷ xs) = Product.map id (x ∷_) (vec-split ρ xs)

  vec-remove : (ρ : n + m ≔ l) → Vec A l → Vec A n
  vec-remove ρ = proj₁ ∘ vec-split ρ

  vec-merge-++ : ∀ (ρ : n + k ≔ l) (xs : Vec A m) {ys : Vec A n} {zs : Vec A k}
               → vec-++ xs (vec-merge ρ ys zs) ≡ vec-merge (extend m ρ) (vec-++ xs ys) zs
  vec-merge-++ ρ [] {ys} {zs}
    rewrite vec-merge-idˡ (left-first′ _ _) ys
    | vec-merge-idˡ (left-first′ _ _) (vec-merge ρ ys zs)
    = refl
  vec-merge-++ ρ (x ∷ xs) = cong (x ∷_) (vec-merge-++ ρ xs)

  module _ {p} {P : A → Set p} where
    all-merge : ∀ (ρ : n + m ≔ l) {xs : Vec A n} {ys : Vec A m}
              → All P xs → All P ys → All P (vec-merge ρ xs ys)
    all-merge zero [] [] = []
    all-merge (left ρ) (x ∷ xs) ys = x ∷ all-merge ρ xs ys
    all-merge (right ρ) xs (y ∷ ys) = y ∷ all-merge ρ xs ys

    all-++ : ∀ {xs : Vec A n} {ys : Vec A m} → All P xs → All P ys → All P (vec-++ xs ys)
    all-++ xs ys = all-merge (left-first′ _ _) xs ys

    all-update : ∀ (ρ : n + 1 ≔ m) {x} {xs} → P x → All P xs → All P (vec-update ρ x xs)
    all-update (left ρ) y (x ∷ xs) = x ∷ all-update ρ y xs
    all-update (right ρ) y (x ∷ xs) = y ∷ xs

    all-split : ∀ (ρ : n + m ≔ l) {xs ys} → All P (vec-merge ρ xs ys) → All P xs × All P ys
    all-split zero {[]} {[]} [] = [] , []
    all-split (left ρ) {x ∷ xs} (p ∷ ps) = Product.map (p ∷_) id (all-split ρ ps)
    all-split (right ρ) {_} {y ∷ ys} (p ∷ ps) = Product.map id (p ∷_) (all-split ρ ps)

    all-remove : ∀ (ρ : n + m ≔ l) {xs ys} → All P (vec-merge ρ xs ys) → All P xs
    all-remove ρ = proj₁ ∘ all-split ρ

    all-merge∘split : ∀ (ρ : n + m ≔ l) xs ys (ps : All P (vec-merge ρ xs ys))
                    → Product.uncurry′ (all-merge ρ) (all-split ρ ps) ≡ ps
    all-merge∘split zero [] [] [] = refl
    all-merge∘split (left ρ) (x ∷ xs) ys (p ∷ ps) = cong (p ∷_) (all-merge∘split ρ _ _ ps)
    all-merge∘split (right ρ) xs (y ∷ ys) (p ∷ ps) = cong (p ∷_) (all-merge∘split ρ _ _ ps)

{-
    open import Relation.Binary.HeterogeneousEquality using (_≅_; icong) renaming (cong to hcong; cong₂ to hcong₂; refl to hrefl)
    all-merge-idˡ : ∀ (ρ : 0 + n ≔ n) {xs} (pxs : All P xs) → all-merge ρ [] pxs ≅ pxs
    all-merge-idˡ zero {[]} [] = hrefl
    all-merge-idˡ (right ρ) {x ∷ xs} (px ∷ pxs) = {!!}

    all-merge-++ : ∀ (ρ : n + k ≔ l) {xs : Vec A m} {ys : Vec A n} {zs : Vec A k}
                 → (pxs : All P xs) {pys : All P ys} {pzs : All P zs}
                 → all-++ pxs (all-merge ρ pys pzs) ≅ all-merge (extend m ρ) (all-++ pxs pys) pzs
    all-merge-++ ρ [] = {!!}
    all-merge-++ ρ (px ∷ pxs) {pys} {pzs} =  hcong₂ _∷_ hrefl (all-merge-++ ρ pxs)
-}
