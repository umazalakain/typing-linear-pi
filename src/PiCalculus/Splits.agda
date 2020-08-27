{-# OPTIONS --safe #-}

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Product as Product using (Σ-syntax; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂) renaming (∃! to ∃!-setoid)

open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
import Data.Nat.Properties as ℕₚ

module PiCalculus.Splits where

∃! : ∀ {a b} {A : Set a} → (A → Set b) → Set _
∃! = ∃!-setoid _≡_

-- TODO: enters the stdlib
infix 5 _<*>_
_<*>_ : ∀ {a p q} {A : Set a} → (A → Set p) → (A → Set q) → (A → Set _)
(f <*> g) i = f i × g i

module _ where
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

  +-identityˡ : zero + n ≔ n
  +-identityˡ {zero} = zero
  +-identityˡ {suc n} = right +-identityˡ

  +-identityʳ : n + zero ≔ n
  +-identityʳ {zero} = zero
  +-identityʳ {suc n} = left +-identityʳ

  +-suc : suc n + m ≔ l → n + suc m ≔ l
  +-suc (left ρ) = right ρ
  +-suc (right ρ) = right (+-suc ρ)

  +-unique : n + m ≔ l → n + m ≔ k → l ≡ k
  +-unique zero zero = refl
  +-unique (left ρ) (left ρ') = cong suc (+-unique ρ ρ')
  +-unique (left ρ) (right ρ') = cong suc (+-unique ρ (+-suc ρ'))
  +-unique (right ρ) (left ρ') = cong suc (+-unique (+-suc ρ) ρ')
  +-unique (right ρ) (right ρ') = cong suc (+-unique ρ ρ')

  +-comm : n + m ≔ l → m + n ≔ l
  +-comm zero = zero
  +-comm (left ρ) = right (+-comm ρ)
  +-comm (right ρ) = left (+-comm ρ)

  +-mk : ∀ n m → ∃! (n + m ≔_)
  +-mk zero m = m , +-identityˡ , +-unique (+-identityˡ)
  +-mk (suc n) m = Product.map suc (Product.map left (λ {s} _ → +-unique (left s))) (+-mk n m)

  _+_ : ℕ → ℕ → ℕ
  n + m = proj₁ (+-mk n m)

  +-assoc : ∃ (n + m ≔_ <*> _+ l ≔ k) → ∃ (m + l ≔_ <*> n +_≔ k)
  +-assoc (_ , zero , r) = _ , +-identityˡ , r
  +-assoc (_ , left l , left r) with _ , l' , r' ← +-assoc (_ , l , r) = _ , l' , left r'
  +-assoc (_ , left l , right r) with _ , l' , r' ← +-assoc (_ , l , +-suc r) = _ , l' , left r'
  +-assoc (_ , right l , left r) with _ , l' , r' ← +-assoc (_ , l , r) = _ , left l' , right r'
  +-assoc (_ , right l , right r) with _ , l' , r' ← +-assoc (_ , l , +-suc r) = _ , left l' , right r'

  +-fromFin : Fin (suc n) → n + 1 ≔ suc n
  +-fromFin zero = right +-identityʳ
  +-fromFin {suc n} (suc i) = left (+-fromFin i)

  +-toFin : n + 1 ≔ m → Fin m
  +-toFin (left s) = suc (+-toFin s)
  +-toFin (right s) = zero

  extend : ∀ k → n + m ≔ l → (k + n) + m ≔ (k + l)
  extend {n = n} {l = l} zero ρ = ρ
  extend {n = n} {l = l} (suc k) ρ = left (extend k ρ)

module _ {a} {A : Set a} where
  open import Level using (_⊔_) renaming (suc to lsuc)
  open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

  private
    variable
      n m l k nm ml : ℕ
      x : A
      xs ys zs ws xys : Vec A n
      ρ ρ' ξ ξ' : n + m ≔ l

  data _>_<_≔_ : Vec A n → n + m ≔ l → Vec A m → Vec A l → Set (lsuc a) where
    zero : [] > zero < [] ≔ []
    left : xs > ρ < ys ≔ zs → (x ∷ xs) > left ρ < ys ≔ (x ∷ zs)
    right : xs > ρ < ys ≔ zs → xs > right ρ < (x ∷ ys) ≔ (x ∷ zs)

  ><-identityˡ : {xs : Vec A n} {ρ : zero + n ≔ n} → [] > ρ < xs ≔ xs
  ><-identityˡ {xs = []} {zero} = zero
  ><-identityˡ {xs = x ∷ xs} {right ρ} = right ><-identityˡ

  ><-unique : xs > ρ < ys ≔ zs → xs > ρ < ys ≔ ws → zs ≡ ws
  ><-unique zero zero = refl
  ><-unique (left ρ) (left ρ') = cong (_ ∷_) (><-unique ρ ρ')
  ><-unique (right ρ) (right ρ') = cong (_ ∷_) (><-unique ρ ρ')

  ><-mk : (ρ : n + m ≔ l) (xs : Vec A n) (ys : Vec A m) → ∃! (xs > ρ < ys ≔_)
  ><-mk zero [] [] = [] , zero , ><-unique zero
  ><-mk (left ρ) (x ∷ xs) ys = Product.map (_ ∷_) (Product.map left (λ {ρ} _ → ><-unique (left ρ))) (><-mk ρ xs ys)
  ><-mk (right ρ) xs (y ∷ ys) = Product.map (_ ∷_) (Product.map right (λ {ρ} _ → ><-unique (right ρ))) (><-mk ρ xs ys)

  _>_<_ : Vec A n → (n + m ≔ l) → Vec A m → Vec A (n + m)
  _>_<_ {n = n} {m = m} xs ρ ys
    with _ , ρ' , uρ' ← +-mk n m
    with refl ← uρ' ρ
    with zs , _ , _ ← ><-mk ρ xs ys
    = zs

  _++_ : Vec A n → Vec A m → Vec A (n + m)
  _++_ {n = n} {m = m} xs ys
    with _ , ρ , uρ ← +-mk n m
    with zs , _ , _ ← ><-mk ρ xs ys
    = zs

  ><-assoc : {xs : Vec A n} {ys : Vec A m} {zs : Vec A l} {ws : Vec A k}
           → (ρ : n + m ≔ nm) (ξ : nm + l ≔ k)
           → ∃ (xs > ρ  < ys ≔_ <*>   _> ξ  < zs ≔ ws)
           → Σ[ ml ∈ ℕ ] Σ[ ρ' ∈ n + ml ≔ k ] Σ[ ξ' ∈ m + l ≔ ml ]
             ∃ (xs > ρ' <_≔ ws  <*> ys > ξ' < zs ≔_)
  ><-assoc zero ξ (_ , zero , r)
    with refl ← +-unique ξ +-identityˡ
    with refl ← ><-unique r ><-identityˡ
    = _ , +-identityˡ , ξ , _ , ><-identityˡ , ><-identityˡ
  ><-assoc .(left _) .(left _) (_ , left l , left r)
    with _ , _ , _ , _ , l' , r' ← ><-assoc _ _ (_ , l , r)
    = _ , _ , _ , _ , left l' , r'
  ><-assoc .(left _) .(right _) (_ , left l , right r)
    with _ , _ , _ , _ , l' , r' ← ><-assoc _ _ (_ , left l , r)
    = _ , _ , _ , _ , right l' , right r'
  ><-assoc .(right _) .(left _) (_ , right l , left r)
    with _ , _ , _ , _ , l' , r' ← ><-assoc _ _ (_ , l , r)
    = _ , _ , _ , _ , right l' , left r'
  ><-assoc (right ρ) (right ξ) (_ , right l , right r)
    with _ , _ , _ , _ , l' , r' ← ><-assoc _ _ (_ , right l , r)
    = _ , _ , _ , _ , right l' , right r'


  module _ {p} {P : A → Set p} where
    private
      variable
        px py : P x
        >ρ< : xs > ρ < ys ≔ zs
        pxs pys pzs pws : All P xs

    data _|>_<|_≔_ : {xs : Vec A n} {ys : Vec A m} {zs : Vec A l} {ρ : n + m ≔ l}
                   → All P xs → xs > ρ < ys ≔ zs → All P ys → All P zs → Set (lsuc (a ⊔ p)) where

      zero  : [] |> zero <| [] ≔ []
      left  : pxs |> >ρ< <| pys ≔ pzs → (px ∷ pxs) |> left >ρ< <| pys ≔ (px ∷ pzs)
      right : pxs |> >ρ< <| pys ≔ pzs → pxs |> right >ρ< <| (px ∷ pys) ≔ (px ∷ pzs)

    |><|-identityˡ : {pxs : All P xs} {>ρ< : [] > ρ < xs ≔ xs} → [] |> >ρ< <| pxs ≔ pxs
    |><|-identityˡ {pxs = []} {>ρ< = zero} = zero
    |><|-identityˡ {pxs = _ ∷ _} {>ρ< = right >ρ<} = right |><|-identityˡ

    |><|-unique : pxs |> >ρ< <| pys ≔ pzs → pxs |> >ρ< <| pys ≔ pws → pzs ≡ pws
    |><|-unique zero zero = refl
    |><|-unique (left ρ) (left ρ') = cong (_ ∷_) (|><|-unique ρ ρ')
    |><|-unique (right ρ) (right ρ') = cong (_ ∷_) (|><|-unique ρ ρ')

    |><|-mk : (>ρ< : xs > ρ < ys ≔ zs) (pxs : All P xs) (pys : All P ys) → ∃! (pxs |> >ρ< <| pys ≔_)
    |><|-mk zero [] [] = [] , zero , |><|-unique zero
    |><|-mk (left ρ) (px ∷ pxs) pys = Product.map (_ ∷_) (Product.map left (λ {>ρ<} _ → |><|-unique (left >ρ<))) (|><|-mk ρ pxs pys)
    |><|-mk (right ρ) pxs (py ∷ pys) = Product.map (_ ∷_) (Product.map right (λ {>ρ<} _ → |><|-unique (right >ρ<))) (|><|-mk ρ pxs pys)

    _|>_<|_ : {xs : Vec A n} {ys : Vec A m} → All P xs → (>ρ< : xs > ρ < ys ≔ zs) → All P ys → All P (xs > ρ < ys)
    _|>_<|_ {n = n} {m = m} {ρ = ρ} {xs = xs} {ys = ys} pxs >ρ< pys
      with _ , ρ' , uρ ← +-mk n m
      with refl ← uρ ρ
      with _ , >ρ<' , u>ρ< ← ><-mk ρ xs ys
      with refl ← u>ρ< >ρ<
      with pzs , _ , _ ← |><|-mk >ρ< pxs pys
      = pzs

    _|++|_ : {xs : Vec A n} {ys : Vec A m} → All P xs → All P ys → All P (xs ++ ys)
    _|++|_ {n = n} {m = m} {xs = xs} {ys = ys} pxs pys
      with _ , ρ , uρ ← +-mk n m
      with _ , >ρ< , u>ρ< ← ><-mk ρ xs ys
      with pzs , _ , _ ← |><|-mk >ρ< pxs pys
      = pzs

    |><|-assoc : {pxs : All P xs} {pys : All P ys} {pzs : All P zs} {pws : All P ws}
               → (>ρ< : xs > ρ < ys ≔ xys) (>ξ< : xys > ξ < zs ≔ ws)
               → ∃ (pxs |> >ρ< <| pys ≔_ <*>   _|> >ξ< <| pzs ≔ pws)
               → Σ[ ml ∈ ℕ ] Σ[ ρ' ∈ n + ml ≔ k ] Σ[ ξ' ∈ m + l ≔ ml ]
                 Σ[ yzs ∈ Vec A ml ] Σ[ >ρ'< ∈ xs > ρ' < yzs ≔ ws ] Σ[ >ξ'< ∈ ys > ξ' < zs ≔ yzs ]
                 ∃ (pxs |> >ρ'< <|_≔ pws <*> pys |> >ξ'< <| pzs ≔_)

    |><|-assoc {ξ = ξ} .zero >ξ< (_ , zero , r)
      with refl ← +-unique ξ +-identityˡ
      with refl ← ><-unique >ξ< ><-identityˡ
      with refl ← |><|-unique r |><|-identityˡ
      = _ , +-identityˡ , +-identityˡ
      , _ , ><-identityˡ , ><-identityˡ
      , _ , |><|-identityˡ , |><|-identityˡ
    |><|-assoc .(left _) .(left _) (_ , left l , left r)
      with _ , _ , _ , _ , _ , _ , _ , l' , r' ← |><|-assoc _ _ (_ , l , r)
      = _ , _ , _ , _ , _ , _ , _ , left l' , r'
    |><|-assoc .(left _) .(right _) (_ , left l , right r)
      with _ , _ , _ , _ , _ , _ , _ , l' , r' ← |><|-assoc _ _ (_ , left l , r)
      = _ , _ , _ , _ , _ , _ , _ , right l' , right r'
    |><|-assoc .(right _) .(left _) (_ , right l , left r)
      with _ , _ , _ , _ , _ , _ , _ , l' , r' ← |><|-assoc _ _ (_ , l , r)
      = _ , _ , _ , _ , _ , _ , _ , right l' , left r'
    |><|-assoc .(right _) .(right _) (_ , right l , right r)
      with _ , _ , _ , _ , _ , _ , _ , l' , r' ← |><|-assoc _ _ (_ , right l , r)
      = _ , _ , _ , _ , _ , _ , _ , right l' , right r'
