{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_; _|>_)

import Data.Nat as ℕ

open import Level using (_⊔_)
open import Data.Empty using (⊥-elim)
open ℕ using (ℕ; zero; suc)

module PiCalculus.Utils where
private
  variable
    n m : ℕ

module ℕₛ where
  import Data.Digit as Digit
  open import Function using (_$_)
  open import Data.Product using (proj₁; _,_)
  open import Data.List.Base using (List; map; reverse)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  open import Data.Vec.Base using (Vec; _∷_; take; lookup; splitAt; _++_)
  open import Data.Vec.Relation.Unary.Any using (here; there)
  open import Data.Char.Base using (Char)
  open import Data.Fin.Base using (Fin; zero; suc; inject≤)
  open import Relation.Nullary.Decidable using (True)
  open import Data.Nat using (_≤_)
  open import Data.Nat.Properties using (_≤?_; m≤m+n)

  import Data.Vec.Membership.Propositional as ∈ᵥ
  import Data.Vec.Membership.Propositional.Properties as ∈ᵥₚ
  import Data.List.Membership.Propositional as ∈ₗ
  import Data.List.Membership.Propositional.Properties as ∈ₗₚ
  import Data.List.Relation.Unary.All as All
  import Data.List.Relation.Unary.All.Properties as Allₚ

  -- Like Data.Nat.Show.toDigitChars but without converting it into a string
  toDigitChars : (base : ℕ)
             {base≥2 : True (2 ≤? base)}
             {base≤16 : True (base ≤? 16)} →
             ℕ → List Char
  toDigitChars base {base≥2} {base≤16} n =
    map (Digit.showDigit {base≤16 = base≤16}) $
    reverse $
    proj₁ $ Digit.toDigits base {base≥2 = base≥2} n

  take-step : ∀ {a} {A : Set a} n {m} x (xs : Vec A (n ℕ.+ m)) → take (suc n) (x ∷ xs) ≡ x ∷ take n xs
  take-step n x xs with splitAt n xs
  take-step n x .(xs ++ ys) | xs , ys , refl = refl

  take-lookup-inject : ∀ {a} {A : Set a} (i : Fin n) (xs : Vec A (n ℕ.+ m)) → lookup xs (inject≤ i (m≤m+n _ _)) ≡ lookup (take n xs) i
  take-lookup-inject {n = suc n} zero (x ∷ xs) rewrite take-step n x xs = refl
  take-lookup-inject {n = suc (suc n)} (suc zero) (x ∷ x' ∷ xs) rewrite take-step (suc n) x (x' ∷ xs) | take-step n x' xs = refl
  take-lookup-inject {n = suc (suc n)} (suc (suc i)) (x ∷ x' ∷ xs) rewrite take-step (suc n) x (x' ∷ xs) | take-step n x' xs = take-lookup-inject i xs

  DECIMALS : Vec Char 10
  DECIMALS = take 10 Digit.digitChars

  showDigit∈digitChars : (d : Digit.Digit 10) → Digit.showDigit d ∈ᵥ.∈ DECIMALS
  showDigit∈digitChars d rewrite take-lookup-inject d Digit.digitChars = ∈ᵥₚ.∈-lookup d DECIMALS

  ∈toDigitChars⇒∈digitChars : ∀ n c → c ∈ₗ.∈ toDigitChars 10 n → c ∈ᵥ.∈ DECIMALS
  ∈toDigitChars⇒∈digitChars n c c∈dC with ∈ₗₚ.∈-map⁻ Digit.showDigit c∈dC
  ∈toDigitChars⇒∈digitChars n c c∈dC | d , _ , refl = showDigit∈digitChars d

module AllAcc {a b} {A : Set a} where
  import Data.Vec as Vec
  open Vec using (Vec; []; _∷_)

  -- Like Data.Vec.Relation.Unary.All, but we also depend on the list constructed so far
  data All (P : ∀ {n} → A → Vec A n → Set b) : ∀ {n} → Vec A n → Set (a ⊔ b) where
    [] : All P []
    _∷_ : ∀ {n x} {xs : Vec A n} → P x xs → All P xs → All P (x ∷ xs)

  open All public

  map : ∀ {c} {C : Set c} {P : ∀ {n} → A → Vec A n → Set b} {xs : Vec A n}
      → (∀ {n x} {xs : Vec A n} → P x xs → C) → All P xs → Vec C n
  map f [] = []
  map f (x ∷ ps) = (f x) ∷ map f ps


module ListInv {a} {A : Set a} where
  import Data.List as List
  import Data.List.Properties as Listₚ
  import Data.List.Membership.Propositional.Properties as ∈ₚ
  import Data.List.Relation.Unary.Any.Properties as Anyₚ
  open import Data.List.Relation.Unary.Any using (Any; here; there)
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Relation.Binary.Equality.Propositional {A = A} using (_≋_; []; _∷_; ≋⇒≡; ≡⇒≋; ≋-refl)
  open List using (List; []; _∷_; [_]; _++_; _∷ʳ_)

  module _ {b} {P : A → Set b} where
    Any-reverse : {xs : List A} → Any P xs → Any P (List.reverse xs)
    Any-reverse {xs = x ∷ xs} (here p) rewrite Listₚ.unfold-reverse x xs = Anyₚ.++⁺ʳ _ (here p)
    Any-reverse {xs = x ∷ xs} (there ps) rewrite Listₚ.unfold-reverse x xs = Anyₚ.++⁺ˡ (Any-reverse ps)

    reverse-Any : {xs : List A} → Any P (List.reverse xs) → Any P xs
    reverse-Any = subst (Any P) (Listₚ.reverse-involutive _) ∘ Any-reverse

  inv-++ˡ' : ∀ lx ly {rx ry} s → s ∉ lx → s ∉ ly → lx ++ [ s ] ++ rx ≋ ly ++ [ s ] ++ ry → lx ≋ ly
  inv-++ˡ' [] [] s ∉lx ∉ly eq = []
  inv-++ˡ' [] (x ∷ ly) .x ∉lx ∉ly (refl ∷ eq) = ⊥-elim (∉ly (here refl))
  inv-++ˡ' (x ∷ lx) [] .x ∉lx ∉ly (refl ∷ eq) = ⊥-elim (∉lx (here refl))
  inv-++ˡ' (x ∷ lx) (.x ∷ ly) s ∉lx ∉ly (refl ∷ eq)
    rewrite ≋⇒≡ (inv-++ˡ' lx ly s (∉lx ∘ there) (∉ly ∘ there) eq) = ≋-refl

  inv-++ˡ : ∀ lx ly {rx ry} s → s ∉ lx → s ∉ ly → lx ++ [ s ] ++ rx ≡ ly ++ [ s ] ++ ry → lx ≡ ly
  inv-++ˡ lx ly s ∉lx ∉ly = ≋⇒≡ ∘ inv-++ˡ' lx ly s ∉lx ∉ly ∘ ≡⇒≋

  reverse-injective : ∀ {xs ys : List A} → List.reverse xs ≡ List.reverse ys → xs ≡ ys
  reverse-injective = subst (_≡ _) (Listₚ.reverse-involutive _)
                    ∘ subst (_ ≡_) (Listₚ.reverse-involutive _)
                    ∘ cong List.reverse

  inv-++ʳ : ∀ lx ly {rx ry} s → s ∉ rx → s ∉ ry → lx ++ [ s ] ++ rx ≡ ly ++ [ s ] ++ ry → rx ≡ ry
  inv-++ʳ lx ly {rx} {ry} s ∉rx ∉ry
    = reverse-injective
    ∘ inv-++ˡ (List.reverse rx) (List.reverse ry) s (∉rx ∘ reverse-Any) (∉ry ∘ reverse-Any)
    ∘ subst (_ ≡_) (do-reverse ly _)
    ∘ subst (_≡ _) (do-reverse lx _)
    ∘ cong List.reverse

    where do-reverse : ∀ (lx rx : List A) {s}
                     → List.reverse (lx ++ [ s ] ++ rx) ≡ List.reverse rx ++ [ s ] ++ List.reverse lx
          do-reverse lx rx {s} = trans (Listₚ.reverse-++-commute lx _)
                                       (trans (cong (_++ List.reverse lx) (Listₚ.unfold-reverse s rx))
                                              (Listₚ.++-assoc (List.reverse rx) _ _))

