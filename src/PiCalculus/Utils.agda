{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym; cong; cong₂; trans; subst₂)
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

module Sum {a b} {A : Set a} {B : Set b} where
  open import Data.Sum.Base
  open import Data.Unit
  open import Data.Empty

  IsInj₁ : A ⊎ B → Set
  IsInj₁ (inj₁ _) = ⊤
  IsInj₁ (inj₂ _) = ⊥

module All2Vec {a b c} {A : Set a} {P : A → Set b} {C : Set c} where
  open import Data.Vec
  open import Data.Vec.Relation.Unary.All

  all2vec : {xs : Vec A n} → (∀ {x} → P x → C) → All P xs → Vec C n
  all2vec f [] = []
  all2vec f (x ∷ xs) = f x ∷ all2vec f xs

module AllAcc {a b} {A : Set a} where
  open import Data.Product using (_×_; _,_; uncurry)
  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Nullary.Product using (_×-dec_)
  open import Relation.Nullary.Decidable using (map′)
  import Data.Vec as Vec
  open Vec using (Vec; []; _∷_)

  -- PR agda-stdlib: https://github.com/agda/agda-stdlib/pull/1256
  data All (P : ∀ {n} → A → Vec A n → Set b) : ∀ {n} → Vec A n → Set (a ⊔ b) where
    [] : All P []
    _∷_ : ∀ {n x} {xs : Vec A n} → P x xs → All P xs → All P (x ∷ xs)

  open All public

  module _ {P : ∀ {n} → A → Vec A n → Set b} where
    uncons : ∀ {x} {xs : Vec A n} → All P (x ∷ xs) → P x xs × All P xs
    uncons (p ∷ ps) = p , ps

    all : (∀ {n} x (xs : Vec A n) → Dec (P x xs)) → (xs : Vec A n) → Dec (All P xs)
    all P? [] = yes []
    all P? (x ∷ xs) = map′ (uncurry _∷_) uncons (P? x xs ×-dec all P? xs)


module ListInv {a} {A : Set a} where
  import Data.List as List
  import Data.List.Properties as Listₚ
  import Data.List.Membership.Propositional.Properties as ∈ₚ
  import Data.List.Relation.Unary.Any.Properties as Anyₚ
  open import Data.List.Relation.Unary.Any using (Any; here; there)
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Relation.Binary.Equality.Propositional {A = A} using (_≋_; []; _∷_; ≋⇒≡; ≡⇒≋; ≋-refl)
  open List using (List; []; _∷_; [_]; _++_; _∷ʳ_)

  -- PR agda-stdlib: https://github.com/agda/agda-stdlib/pull/1251
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
  reverse-injective = subst₂ _≡_ (Listₚ.reverse-involutive _) (Listₚ.reverse-involutive _) ∘ cong List.reverse

  inv-++ʳ : ∀ lx ly {rx ry} s → s ∉ rx → s ∉ ry → lx ++ [ s ] ++ rx ≡ ly ++ [ s ] ++ ry → rx ≡ ry
  inv-++ʳ lx ly {rx} {ry} s ∉rx ∉ry
    = reverse-injective
    ∘ inv-++ˡ (List.reverse rx) (List.reverse ry) s (∉rx ∘ reverse-Any) (∉ry ∘ reverse-Any)
    ∘ subst₂ _≡_ (do-reverse lx _) (do-reverse ly _)
    ∘ cong List.reverse

    where do-reverse : ∀ (lx rx : List A) {s}
                     → List.reverse (lx ++ [ s ] ++ rx) ≡ List.reverse rx ++ [ s ] ++ List.reverse lx
          do-reverse lx rx {s} = trans (Listₚ.reverse-++-commute lx _)
                                       (trans (cong (_++ List.reverse lx) (Listₚ.unfold-reverse s rx))
                                              (Listₚ.++-assoc (List.reverse rx) _ _))

module ℕₛ where
  import Data.Digit as Digit
  open import Function using (_$_)
  open import Data.Product using (proj₁; _,_)
  open import Data.List.Base using (List; map; reverse; []; _∷_)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  open import Data.Vec.Base using (Vec; _∷_; take; lookup; splitAt; _++_)
  open import Data.Vec.Relation.Unary.Any using (here; there)
  open import Data.Char.Base using (Char)
  open import Data.Fin.Base using (Fin; zero; suc; inject≤)
  open import Relation.Nullary.Decidable using (True)
  open import Data.Nat using (_≤_)
  open import Data.Nat.Properties using (_≤?_; m≤m+n)
  open import Data.List.Relation.Binary.Equality.Propositional using (_≋_; ≡⇒≋; ≋⇒≡; []; _∷_)

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

  -- PR stdlib https://github.com/agda/agda-stdlib/pull/1250
  -- PR stdlib https://github.com/agda/agda-stdlib/pull/1255
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

  toDigits-injective : ∀ n m → proj₁ (Digit.toDigits 10 n) ≡ proj₁ (Digit.toDigits 10 m) → n ≡ m
  toDigits-injective n m eq with Digit.toDigits 10 n | Digit.toDigits 10 m
  toDigits-injective .(Digit.fromDigits exp1) .(Digit.fromDigits exp2) eq | exp1 , refl | exp2 , refl = cong Digit.fromDigits eq

  open AllAcc using ([]; _∷_)

  open import Relation.Nullary using (Dec)
  open import Relation.Nullary.Decidable using (toWitness; True)
  open import Relation.Nullary.Negation using (¬?)
  open import Data.Vec.Relation.Unary.Any using (any)
  open import Data.Char.Properties as Charₚ

  module _ {a} {A : Set a} where
    Fresh : Vec A n → Set a
    Fresh = AllAcc.All λ x xs → x ∈ᵥ.∉ xs

    lookup-fresh-injective : {xs : Vec A n} → Fresh xs → ∀ i j → lookup xs i ≡ lookup xs j → i ≡ j
    lookup-fresh-injective fs zero zero eq = refl
    lookup-fresh-injective (p ∷ ps) zero (suc j) refl = ⊥-elim (p (∈ᵥₚ.∈-lookup _ _))
    lookup-fresh-injective (p ∷ ps) (suc i) zero refl = ⊥-elim (p (∈ᵥₚ.∈-lookup _ _))
    lookup-fresh-injective (p ∷ ps) (suc i) (suc j) eq = cong suc (lookup-fresh-injective ps i j eq)

    decidable : ((x y : A) → Dec (x ≡ y)) → (xs : Vec A n) → Dec (Fresh xs)
    decidable f = AllAcc.all λ x → ¬? ∘ any (f x)

  decimalsFresh : {True (decidable Charₚ._≟_ DECIMALS)} → Fresh DECIMALS
  decimalsFresh {t} = toWitness {Q = decidable Charₚ._≟_ DECIMALS} t

  showDigit-injective : ∀ (n m : Digit.Digit 10) → Digit.showDigit n ≡ Digit.showDigit m → n ≡ m
  showDigit-injective n m
    rewrite take-lookup-inject n Digit.digitChars
    | take-lookup-inject m Digit.digitChars
    = lookup-fresh-injective decimalsFresh n m


  module _ {a b} {A : Set a} {B : Set b} where
    map-preserves-injectivity : {f : A → B} (xs ys : List A) → (∀ x y → f x ≡ f y → x ≡ y) → map f xs ≋ map f ys → xs ≋ ys
    map-preserves-injectivity List.[] List.[] f-inj [] = [] {A = A}
    map-preserves-injectivity (x List.∷ xs) (y List.∷ ys) f-inj (x~y ∷ r) = _∷_ {A = A} (f-inj x y x~y) (map-preserves-injectivity xs ys f-inj r)

  -- PR agda-stdlib WIP
  toDigitChars-injective : ∀ n m → toDigitChars 10 n ≡ toDigitChars 10 m → n ≡ m
  toDigitChars-injective n m = toDigits-injective _ _
                             ∘ ListInv.reverse-injective
                             ∘ ≋⇒≡
                             ∘ map-preserves-injectivity _ _ showDigit-injective
                             ∘ ≡⇒≋
