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
  open Raw
  open Scoped

  open import Level using (Lift)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
  open import Function using (_∘_)
  open import Relation.Nullary using (Dec; yes; no; _because_)
  open import Relation.Nullary.Decidable using (True; toWitness)

  open import Data.Empty using (⊥)
  open import Data.Bool.Base using (Bool; true; false)
  open import Data.Product using (_,_; _×_; proj₁; proj₂)
  open import Data.Unit using (⊤; tt)
  open import Data.Nat.Base using (ℕ; zero; suc)
  open import Data.Nat.Show using (show)
  open import Data.Fin.Base using (Fin; zero; suc)
  open import Data.Vec.Base using (Vec; []; _∷_; lookup)
  open import Data.String.Base using (_++_)
  open import Data.Vec.Relation.Unary.Any using (index)

  open import Relation.Nullary.Product using (_×-dec_)
  open import Relation.Nullary.Negation using (¬?)
  import Data.String.Properties as Stringₚ
  open import Data.Vec.Membership.Propositional using (_∈_; _∉_)
  open import Data.Vec.Relation.Unary.Any using (here; there)
  import Data.Vec.Membership.DecPropositional as DecPropositional
  _∈?_ = DecPropositional._∈?_ Stringₚ._≟_

  private
    variable
      n m : ℕ

  Counter : Set
  Counter = Name → ℕ

  init : Counter
  init _ = zero

  inc : Counter → Name → Counter
  inc counter name x with name Stringₚ.≟ x
  inc counter name x | true because _ = suc (counter x)
  inc counter name x | false because _ = counter x

  fresh' : Counter → Vec Name n → Name → Name
  fresh' counter [] hint = hint
  fresh' counter (name ∷ ctx) hint = fresh' (inc counter name) ctx hint

  fresh : Vec Name n → Name → Name
  fresh = fresh' init

  WellScoped : Vec Name n → Raw → Set
  WellScoped ctx 𝟘 = ⊤
  WellScoped ctx (⦅υ x ⦆ P) = WellScoped (x ∷ ctx) P
  WellScoped ctx (P ∥ Q) = WellScoped ctx P × WellScoped ctx Q
  WellScoped ctx (x ⦅ y ⦆ P) = (x ∈ ctx) × WellScoped (y ∷ ctx) P
  WellScoped ctx (x ⟨ y ⟩ P) = (x ∈ ctx) × (y ∈ ctx) × WellScoped ctx P

  WellScoped? : (ctx : Vec Name n) (P : Raw) → Dec (WellScoped ctx P)
  WellScoped? ctx 𝟘 = yes tt
  WellScoped? ctx (⦅υ x ⦆ P) = WellScoped? (x ∷ ctx) P
  WellScoped? ctx (P ∥ Q) = WellScoped? ctx P ×-dec WellScoped? ctx Q
  WellScoped? ctx (x ⦅ y ⦆ P) = x ∈? ctx ×-dec WellScoped? (y ∷ ctx) P
  WellScoped? ctx (x ⟨ y ⟩ P) = x ∈? ctx ×-dec y ∈? ctx ×-dec WellScoped? ctx P

  NotShadowed : Vec Name n → Raw → Set
  NotShadowed ctx 𝟘 = ⊤
  NotShadowed ctx (⦅υ name ⦆ P) = name ∉ ctx × NotShadowed (name ∷ ctx) P
  NotShadowed ctx (P ∥ Q) = NotShadowed ctx P × NotShadowed ctx Q
  NotShadowed ctx (x ⦅ y ⦆ P) = y ∉ ctx × NotShadowed (y ∷ ctx) P
  NotShadowed ctx (x ⟨ y ⟩ P) = NotShadowed ctx P

  NotShadowed? : (ctx : Vec Name n) (P : Raw) → Dec (NotShadowed ctx P)
  NotShadowed? ctx 𝟘 = yes tt
  NotShadowed? ctx (⦅υ name ⦆ P) = ¬? (name ∈? ctx) ×-dec NotShadowed? (name ∷ ctx) P
  NotShadowed? ctx (P ∥ Q) = NotShadowed? ctx P ×-dec NotShadowed? ctx Q
  NotShadowed? ctx (x ⦅ y ⦆ P) = ¬? (y ∈? ctx) ×-dec NotShadowed? (y ∷ ctx) P
  NotShadowed? ctx (x ⟨ y ⟩ P) = NotShadowed? ctx P

  ∈toFin : ∀ {a} {A : Set a} {x} {xs : Vec A n} → x ∈ xs → Fin n
  ∈toFin (here px) = zero
  ∈toFin (there x∈xs) = suc (∈toFin x∈xs)

  fromRaw' : (ctx : Vec Name n) (P : Raw) → WellScoped ctx P → Scoped n
  fromRaw' ctx 𝟘 tt = 𝟘
  fromRaw' ctx (⦅υ x ⦆ P) wsP =
    υ (fromRaw' (x ∷ ctx) P wsP) ⦃ x ⦄
  fromRaw' ctx (P ∥ Q) (wsP , wsQ) =
    fromRaw' ctx P wsP ∥ fromRaw' ctx Q wsQ
  fromRaw' ctx (x ⦅ y ⦆ P) (x∈ctx , wsP) =
    (∈toFin x∈ctx ⦅⦆ fromRaw' (y ∷ ctx) P wsP) ⦃ y ⦄
  fromRaw' ctx (x ⟨ y ⟩ P) (x∈ctx , y∈ctx , wsP) =
    ∈toFin x∈ctx ⟨ ∈toFin y∈ctx ⟩ fromRaw' ctx P wsP

  fromRaw : (ctx : Vec Name n) (P : Raw) → ⦃ _ : True (WellScoped? ctx P) ⦄ → Scoped n
  fromRaw ctx P ⦃ p ⦄ = fromRaw' ctx P (toWitness p)

  toRaw : Vec Name n → Scoped n → Raw
  toRaw ctx 𝟘 = 𝟘
  toRaw ctx (υ P ⦃ name ⦄) =
    let name' = fresh ctx name in
    ⦅υ name' ⦆ toRaw (name' ∷ ctx) P
  toRaw ctx (P ∥ Q) =
    toRaw ctx P ∥ toRaw ctx Q
  toRaw ctx ((x ⦅⦆ P) ⦃ name ⦄) =
    let name' = fresh ctx name in
    lookup ctx x ⦅ name' ⦆ toRaw (name' ∷ ctx) P
  toRaw ctx (x ⟨ y ⟩ P) =
    lookup ctx x ⟨ lookup ctx y ⟩ toRaw ctx P

  map : ∀ {a} (B : Scoped n → Set a) (ctx : Vec Name n) (P : Raw) → Set a
  map B ctx P with WellScoped? ctx P
  map B ctx P | yes wsP = B (fromRaw' ctx P wsP)
  map B ctx P | no _ = Lift _ ⊥

  map₂ : ∀ {a} (B : Scoped n → Scoped n → Set a) (ctx : Vec Name n) (P Q : Raw) → Set a
  map₂ B ctx P Q with WellScoped? ctx P | WellScoped? ctx Q
  map₂ B ctx P Q | yes wsP | yes wsQ = B (fromRaw' ctx P wsP) (fromRaw' ctx Q wsQ)
  map₂ B ctx P Q | _       | _       = Lift _ ⊥
