{-# OPTIONS --safe --without-K #-}

open import Data.String.Base using (String)

module PiCalculus.Syntax where

Name : Set
Name = String

module Raw where
  infix 20 _∥_
  infixr 15 ⦅υ_⦆_
  infixr 9 _⦅_⦆_
  infixr 9 _⟨_⟩_

  data Raw : Set where
    𝟘     : Raw
    ⦅υ_⦆_ : Name → Raw → Raw
    _∥_   : Raw → Raw → Raw
    _⦅_⦆_ : Name → Name → Raw → Raw
    _⟨_⟩_ : Name → Name → Raw → Raw


module Scoped where
  open import Data.Fin.Base
  open import Data.Nat.Base

  infix 20 _∥_
  infixr 15 υ
  infixr 9 _⦅⦆_
  infixr 9 _⟨_⟩_

  private
    variable
      n : ℕ

  data Scoped : ℕ → Set where
    𝟘     : Scoped n
    υ : Scoped (suc n) → ⦃ name : Name ⦄ → Scoped n
    _∥_   : Scoped n → Scoped n → Scoped n
    _⦅⦆_ : Fin n → Scoped (suc n) → ⦃ name : Name ⦄ → Scoped n
    _⟨_⟩_ : Fin n → Fin n → Scoped n → Scoped n

module Conversion where
  private
    open Raw
    open Scoped

    open import Level using (Lift; _⊔_)
    open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
    open import Function using (_∘_)
    open import Relation.Nullary using (Dec; yes; no; _because_)
    open import Relation.Nullary.Decidable using (True; toWitness)
    open import Relation.Nullary.Product using (_×-dec_)
    open import Relation.Nullary.Negation using (¬?)

    import Data.Vec.Base as Vec
    import Data.Char.Base as Char
    import Data.List.Base as List
    import Data.String.Base as String
    import Data.String.Properties as Stringₚ
    import Data.Vec.Membership.DecPropositional as DecPropositional

    open import Data.Empty using (⊥)
    open import Data.Bool.Base using (true; false)
    open import Data.Product using (_,_; _×_; Σ)
    open import Data.Unit using (⊤; tt)
    open import Data.Nat.Base using (ℕ; zero; suc)
    open import Data.Fin.Base using (Fin; zero; suc)
    open import Data.String.Base using (_++_)
    open import Data.Vec.Membership.Propositional using (_∈_; _∉_)
    open import Data.Vec.Relation.Unary.Any using (here; there)

    open Vec using (Vec; []; _∷_)
    open List using (List; []; _∷_)

    _∈?_ = DecPropositional._∈?_ Stringₚ._≟_

    import PiCalculus.Utils
    module AllAcc = PiCalculus.Utils.AllAcc
    module ℕₛ = PiCalculus.Utils.ℕₛ
    open AllAcc using ([]; _∷_)

    variable
      n m : ℕ

  Ctx : ℕ → Set
  Ctx = Vec Name

  count : Name → Ctx n → ℕ
  count hint [] = zero
  count hint (name ∷ ctx) with name Stringₚ.≟ hint
  count hint (name ∷ ctx) | true because _ = suc (count hint ctx)
  count hint (name ∷ ctx) | false because _ = count hint ctx

  CountedName : Name → Ctx n → Set
  CountedName name ctx = Σ ℕ (count name ctx ≡_)

  Fresh : Ctx n → Set
  Fresh = AllAcc.All CountedName

  -- From contexts to name counts
  fresh : ∀ name (ctx : Ctx n) → CountedName name ctx
  fresh hint ctx = count hint ctx , refl

  -- From name counts to tuples
  erase : ∀ {x} (xs : Vec Name n) → CountedName x xs → Name × ℕ
  erase {x = x} xs (i , _) = x , i

  -- From tuples to strings, convert to lists first so that we can reason about it
  toCharList : Name × ℕ → List Char.Char
  toCharList (x , i) = String.toList x List.++ ('^' ∷ ℕₛ.toDigitChars 10 i)

  toString : Name × ℕ → Name
  toString = String.fromList ∘ toCharList

  repr : ∀ {x} (xs : Vec Name n) → CountedName x xs → Name
  repr xs = toString ∘ erase xs

  apply : {ctx : Ctx n} → Fresh ctx → Ctx n
  apply = Vec.map toString ∘ AllAcc.map λ { {xs = xs} → erase xs}

  WellScoped : Ctx n → Raw → Set
  WellScoped ctx 𝟘 = ⊤
  WellScoped ctx (⦅υ x ⦆ P) = WellScoped (x ∷ ctx) P
  WellScoped ctx (P ∥ Q) = WellScoped ctx P × WellScoped ctx Q
  WellScoped ctx (x ⦅ y ⦆ P) = (x ∈ ctx) × WellScoped (y ∷ ctx) P
  WellScoped ctx (x ⟨ y ⟩ P) = (x ∈ ctx) × (y ∈ ctx) × WellScoped ctx P

  WellScoped? : (ctx : Ctx n) (P : Raw) → Dec (WellScoped ctx P)
  WellScoped? ctx 𝟘 = yes tt
  WellScoped? ctx (⦅υ x ⦆ P) = WellScoped? (x ∷ ctx) P
  WellScoped? ctx (P ∥ Q) = WellScoped? ctx P ×-dec WellScoped? ctx Q
  WellScoped? ctx (x ⦅ y ⦆ P) = x ∈? ctx ×-dec WellScoped? (y ∷ ctx) P
  WellScoped? ctx (x ⟨ y ⟩ P) = x ∈? ctx ×-dec y ∈? ctx ×-dec WellScoped? ctx P

  NotShadowed : Ctx n → Raw → Set
  NotShadowed ctx 𝟘 = ⊤
  NotShadowed ctx (⦅υ name ⦆ P) = name ∉ ctx × NotShadowed (name ∷ ctx) P
  NotShadowed ctx (P ∥ Q) = NotShadowed ctx P × NotShadowed ctx Q
  NotShadowed ctx (x ⦅ y ⦆ P) = y ∉ ctx × NotShadowed (y ∷ ctx) P
  NotShadowed ctx (x ⟨ y ⟩ P) = NotShadowed ctx P

  NotShadowed? : (ctx : Ctx n) (P : Raw) → Dec (NotShadowed ctx P)
  NotShadowed? ctx 𝟘 = yes tt
  NotShadowed? ctx (⦅υ name ⦆ P) = ¬? (name ∈? ctx) ×-dec NotShadowed? (name ∷ ctx) P
  NotShadowed? ctx (P ∥ Q) = NotShadowed? ctx P ×-dec NotShadowed? ctx Q
  NotShadowed? ctx (x ⦅ y ⦆ P) = ¬? (y ∈? ctx) ×-dec NotShadowed? (y ∷ ctx) P
  NotShadowed? ctx (x ⟨ y ⟩ P) = NotShadowed? ctx P

  ∈toFin : ∀ {a} {A : Set a} {x} {xs : Vec A n} → x ∈ xs → Fin n
  ∈toFin (here px) = zero
  ∈toFin (there x∈xs) = suc (∈toFin x∈xs)

  fromRaw' : (ctx : Ctx n) (P : Raw) → WellScoped ctx P → Scoped n
  fromRaw' ctx 𝟘 tt = 𝟘
  fromRaw' ctx (⦅υ x ⦆ P) wsP =
    υ (fromRaw' (x ∷ ctx) P wsP) ⦃ x ⦄
  fromRaw' ctx (P ∥ Q) (wsP , wsQ) =
    fromRaw' ctx P wsP ∥ fromRaw' ctx Q wsQ
  fromRaw' ctx (x ⦅ y ⦆ P) (x∈ctx , wsP) =
    (∈toFin x∈ctx ⦅⦆ fromRaw' (y ∷ ctx) P wsP) ⦃ y ⦄
  fromRaw' ctx (x ⟨ y ⟩ P) (x∈ctx , y∈ctx , wsP) =
    ∈toFin x∈ctx ⟨ ∈toFin y∈ctx ⟩ fromRaw' ctx P wsP

  fromRaw : (ctx : Ctx n) (P : Raw) → ⦃ _ : True (WellScoped? ctx P) ⦄ → Scoped n
  fromRaw ctx P ⦃ p ⦄ = fromRaw' ctx P (toWitness p)

  toRaw : {ctx : Ctx n} → Fresh ctx → Scoped n → Raw
  toRaw {ctx = ctx} isf 𝟘 = 𝟘
  toRaw {ctx = ctx} isf (υ P ⦃ name ⦄) =
    let cname = fresh name ctx in
    ⦅υ repr ctx cname ⦆ toRaw (cname ∷ isf) P
  toRaw {ctx = ctx} isf (P ∥ Q) =
    toRaw isf P ∥ toRaw isf Q
  toRaw {ctx = ctx} isf ((x ⦅⦆ P) ⦃ name ⦄) =
    let cname = fresh name ctx in
    Vec.lookup (apply isf) x ⦅ repr ctx cname ⦆ toRaw (cname ∷ isf) P
  toRaw {ctx = ctx} isf (x ⟨ y ⟩ P) =
    Vec.lookup (apply isf) x ⟨ Vec.lookup (apply isf) y ⟩ toRaw isf P

  map : ∀ {a} (B : Scoped n → Set a) (ctx : Vec Name n) (P : Raw) → Set a
  map B ctx P with WellScoped? ctx P
  map B ctx P | yes wsP = B (fromRaw' ctx P wsP)
  map B ctx P | no _ = Lift _ ⊥

  map₂ : ∀ {a} (B : Scoped n → Scoped n → Set a) (ctx : Vec Name n) (P Q : Raw) → Set a
  map₂ B ctx P Q with WellScoped? ctx P | WellScoped? ctx Q
  map₂ B ctx P Q | yes wsP | yes wsQ = B (fromRaw' ctx P wsP) (fromRaw' ctx Q wsQ)
  map₂ B ctx P Q | _       | _       = Lift _ ⊥
