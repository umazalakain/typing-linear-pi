open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)

import Data.Nat.Base as ℕ
import Data.Unit.Base as Unit
import Data.Empty as Empty
import Data.Nat.Properties as ℕₚ
import Data.Vec.Base as Vec
import Data.Vec.Properties as Vecₚ
import Data.Vec.Relation.Unary.All as All
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
import Data.Product as Product

open Empty using (⊥)
open Unit using (⊤; tt)
open Product using (_×_; _,_; proj₁; proj₂)
open ℕ using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Pointwise using (Pointwise; []; _∷_)

open import PiCalculus.Function using (_⊗_; _&_)

module PiCalculus.LinearTypeSystem.OmegaNat where

data ωℕ : Set where
  ω∙ : ωℕ
  n∙ : ℕ → ωℕ

pattern 0∙ = n∙ 0
pattern 1∙ = n∙ 1

-- Addition

_+_ : ωℕ → ωℕ → ωℕ
ω∙   + _    = ω∙
n∙ _ + ω∙   = ω∙
n∙ x + n∙ y = n∙ (x ℕ.+ y)

+-idˡ : ∀ x → 0∙ + x ≡ x
+-idˡ ω∙ = refl
+-idˡ (n∙ x) = refl

+-idʳ : ∀ x → x + 0∙ ≡ x
+-idʳ ω∙ = refl
+-idʳ (n∙ x) = n∙ & ℕₚ.+-identityʳ x

+-ωʳ : ∀ x → x + ω∙ ≡ ω∙
+-ωʳ ω∙ = refl
+-ωʳ (n∙ x) = refl

+-comm : ∀ x y → x + y ≡ y + x
+-comm ω∙ ω∙ = refl
+-comm ω∙ (n∙ y) = refl
+-comm (n∙ x) ω∙ = refl
+-comm (n∙ x) (n∙ y) = n∙ & ℕₚ.+-comm x y

-- Substraction

_∸_ : ωℕ → ωℕ → ωℕ
ω∙   ∸ _    = ω∙
n∙ _ ∸ ω∙   = 0∙
n∙ x ∸ n∙ y = n∙ (x ℕ.∸ y)

consume : ωℕ → ωℕ
consume m = m ∸ m

is-consumed : ωℕ → Set
is-consumed ω∙ = ⊤
is-consumed (n∙ zero) = ⊤
is-consumed (n∙ (suc x)) = ⊥

consume-is-consumed : ∀ n → is-consumed (consume n)
consume-is-consumed ω∙ = tt
consume-is-consumed (n∙ zero) = tt
consume-is-consumed (n∙ (suc x)) rewrite ℕₚ.n∸n≡0 x = tt

+-+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-+-assoc ω∙ y z = refl
+-+-assoc (n∙ x) ω∙ z = refl
+-+-assoc (n∙ x) (n∙ y) ω∙ = refl
+-+-assoc (n∙ x) (n∙ y) (n∙ z) = n∙ & ℕₚ.+-assoc x y z

{-
+-∸-assoc : ∀ x {y z} → z ≤ y → (x + y) ∸ z ≡ x + (y ∸ z)
+-∸-assoc x {ω∙} {z} n≤ω rewrite +-ωʳ x = refl
+-∸-assoc ω∙ {.(n∙ _)} {.(n∙ _)} (n≤m _) = refl
+-∸-assoc (n∙ x) {.(n∙ _)} {.(n∙ _)} (n≤m #n≤#m) = n∙ & ℕₚ.+-∸-assoc _ #n≤#m

≤-∸ : ∀ (m n) → (m ∸ n) ≤ m
≤-∸ ω∙ n = n≤ω
≤-∸ (n∙ m) ω∙ = n≤m ℕ.z≤n
≤-∸ (n∙ m) (n∙ n) = n≤m (ℕₚ.m∸n≤m m n)
-}

-- Preservation of infinity

data _~ω~_ : ωℕ → ωℕ → Set where
  ω~ω : ω∙ ~ω~ ω∙
  n~n : ∀ {m n} → n∙ m ~ω~ n∙ n

ω-refl : ∀ {m} → m ~ω~ m
ω-refl {ω∙} = ω~ω
ω-refl {n∙ x} = n~n

ω-sym : ∀ {m n} → m ~ω~ n → n ~ω~ m
ω-sym ω~ω = ω~ω
ω-sym n~n = n~n

ω-trans : ∀ {m n l} → m ~ω~ n → n ~ω~ l → m ~ω~ l
ω-trans ω~ω ω~ω = ω~ω
ω-trans n~n n~n = n~n

ω-cong : ∀ {m n} l → m ~ω~ n → (l + m) ~ω~ (l + n)
ω-cong ω∙ mn = ω~ω
ω-cong (n∙ x) ω~ω = ω~ω
ω-cong (n∙ x) n~n = n~n

ω-idˡ : ∀ {m n} → m ~ω~ n → m ~ω~ (m + n)
ω-idˡ ω~ω = ω~ω
ω-idˡ n~n = n~n

ω-idʳ : ∀ {m n} → m ~ω~ n → m ~ω~ (n + m)
ω-idʳ ω~ω = ω~ω
ω-idʳ n~n = n~n

ω? : ∀ x y → Dec (x ~ω~ y)
ω? ω∙ ω∙ = yes ω~ω
ω? ω∙ (n∙ _) = no (λ ())
ω? (n∙ _) ω∙ = no (λ ())
ω? (n∙ _) (n∙ _) = yes n~n

ω-consume : ∀ m → consume m ~ω~ m
ω-consume ω∙ = ω~ω
ω-consume (n∙ x) = n~n

+-∸-idˡ : ∀ {m n} → m ~ω~ n → (n ∸ n) + m ≡ m
+-∸-idˡ ω~ω = refl
+-∸-idˡ {_} {n∙ m} n~n rewrite ℕₚ.n∸n≡0 m = refl

{-
∸-ω-≤ : ∀ {n m} → n ≤ m → (m ∸ n) ~ω~ m
∸-ω-≤ n≤ω = ω~ω
∸-ω-≤ (n≤m x) = n~n
-}

-- Lift operations, relations and properties to vectors

private
  variable
    n : ℕ

0s : ∀ {n} → Vec ωℕ n
0s = Vec.replicate 0∙

_+ᵥ_ : Vec ωℕ n → Vec ωℕ n → Vec ωℕ n
_+ᵥ_ = Vec.zipWith _+_

+ᵥ-idˡ : ∀ (ns : Vec ωℕ n) → 0s +ᵥ ns ≡ ns
+ᵥ-idˡ = Vecₚ.zipWith-identityˡ +-idˡ

+ᵥ-comm : (ms ns : Vec ωℕ n) → ms +ᵥ ns ≡ ns +ᵥ ms
+ᵥ-comm = Vecₚ.zipWith-comm +-comm

_∸ᵥ_ : Vec ωℕ n → Vec ωℕ n → Vec ωℕ n
_∸ᵥ_ = Vec.zipWith _∸_

consumeᵥ : Vec ωℕ n → Vec ωℕ n
consumeᵥ = Vec.map consume

_~ω~ᵥ_ : (ms ns : Vec ωℕ n) → Set
_~ω~ᵥ_ = Pointwise _~ω~_

ωᵥ? : (ms ns : Vec ωℕ n) → Dec (ms ~ω~ᵥ ns)
ωᵥ? = Pointwise.decidable ω?

ωᵥ-refl : {ms : Vec ωℕ n} → ms ~ω~ᵥ ms
ωᵥ-refl = Pointwise.refl ω-refl

ωᵥ-sym : ∀ {ms ns : Vec ωℕ n} → ms ~ω~ᵥ ns → ns ~ω~ᵥ ms
ωᵥ-sym = Pointwise.sym ω-sym

ωᵥ-trans : {ms ns ls : Vec ωℕ n} → ms ~ω~ᵥ ns → ns ~ω~ᵥ ls → ms ~ω~ᵥ ls
ωᵥ-trans = Pointwise.trans ω-trans

ωᵥ-cong : ∀ {ms ns : Vec ωℕ n} (ls : Vec ωℕ n) → ms ~ω~ᵥ ns → (ls +ᵥ ms) ~ω~ᵥ (ls +ᵥ ns)
ωᵥ-cong [] [] = []
ωᵥ-cong (l ∷ ls) (mn ∷ msns) = ω-cong l mn ∷ ωᵥ-cong ls msns

ωᵥ-idˡ : ∀ {ms ns : Vec ωℕ n} → ms ~ω~ᵥ ns → ms ~ω~ᵥ (ms +ᵥ ns)
ωᵥ-idˡ [] = []
ωᵥ-idˡ (mn ∷ msns) = ω-idˡ mn ∷ ωᵥ-idˡ msns

ωᵥ-idʳ : ∀ {ms ns : Vec ωℕ n} → ms ~ω~ᵥ ns → ms ~ω~ᵥ (ns +ᵥ ms)
ωᵥ-idʳ [] = []
ωᵥ-idʳ (mn ∷ msns) = ω-idʳ mn ∷ ωᵥ-idʳ msns

+ᵥ-∸ᵥ-idˡ : ∀ {ms ns : Vec ωℕ n} → ms ~ω~ᵥ ns → (ns ∸ᵥ ns) +ᵥ ms ≡ ms
+ᵥ-∸ᵥ-idˡ {_} {[]} {[]} [] = refl
+ᵥ-∸ᵥ-idˡ {_} {m ∷ ms} {n ∷ ns} (mωn ∷ msωns) = _∷_ & +-∸-idˡ mωn ⊗ +ᵥ-∸ᵥ-idˡ msωns

{-
≤ᵥ-+ᵥˡ : ∀ {ms ns : Vec ωℕ n} (ls : Vec ωℕ n) → ms ≤ᵥ ns → ms ≤ᵥ (ls +ᵥ ns)
≤ᵥ-+ᵥˡ [] [] = []
≤ᵥ-+ᵥˡ (l ∷ ls) (m≤n ∷ ms≤ᵥns) = ≤-+ˡ l m≤n ∷ ≤ᵥ-+ᵥˡ ls ms≤ᵥns
-}

+ᵥ-+ᵥ-assoc : ∀ (xs ys zs : Vec ωℕ n) → (xs +ᵥ ys) +ᵥ zs ≡ xs +ᵥ (ys +ᵥ zs)
+ᵥ-+ᵥ-assoc [] [] [] = refl
+ᵥ-+ᵥ-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = _∷_ & +-+-assoc x y z ⊗ +ᵥ-+ᵥ-assoc xs ys zs

{-
+ᵥ-∸ᵥ-assoc : (ms : Vec ωℕ n) {ns ls : Vec ωℕ n} → ls ≤ᵥ ns → (ms +ᵥ ns) ∸ᵥ ls ≡ ms +ᵥ (ns ∸ᵥ ls)
+ᵥ-∸ᵥ-assoc [] [] = refl
+ᵥ-∸ᵥ-assoc (m ∷ ms) (l≤n ∷ ls≤ᵥns) = _∷_ & +-∸-assoc m l≤n
                                          ⊗ +ᵥ-∸ᵥ-assoc ms ls≤ᵥns

∸ᵥ-ωᵥ-≤ᵥ : {ms ns : Vec ωℕ n} → ns ≤ᵥ ms → (ms ∸ᵥ ns) ~ω~ᵥ ms
∸ᵥ-ωᵥ-≤ᵥ [] = []
∸ᵥ-ωᵥ-≤ᵥ (n≤m' ∷ ns≤ᵥms) = ∸-ω-≤ n≤m' ∷ ∸ᵥ-ωᵥ-≤ᵥ ns≤ᵥms

≤ᵥ-∸ᵥ : (ms ns : Vec ωℕ n) → (ms ∸ᵥ ns) ≤ᵥ ms
≤ᵥ-∸ᵥ [] [] = []
≤ᵥ-∸ᵥ (m ∷ ms) (n ∷ ns) = ≤-∸ m n ∷ ≤ᵥ-∸ᵥ ms ns
-}
