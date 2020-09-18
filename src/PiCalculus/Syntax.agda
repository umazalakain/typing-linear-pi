{-# OPTIONS --safe --without-K #-}

open import Data.Char.Base using (Char)
open import Data.List.Base using (List; []; _∷_)

module PiCalculus.Syntax where

Name : Set
Name = List Char

module Raw where
  infixr 20 _∥_
  infixr 15 ⦅ν_⦆_
  infixr 10 _⦅_⦆_ _⟨_⟩_

  data Raw : Set where
    𝟘     : Raw
    ⦅ν_⦆_ : Name → Raw → Raw
    _∥_   : Raw → Raw → Raw
    _⦅_⦆_ : Name → Name → Raw → Raw
    _⟨_⟩_ : Name → Name → Raw → Raw


module Scoped where
  open import Data.Fin.Base
  open import Data.Nat.Base

  infixr 20 _∥_
  infixr 15 ν
  infixr 10 _⦅⦆_ _⟨_⟩_

  private
    variable
      n : ℕ

  data Scoped : ℕ → Set where
    𝟘     : Scoped n
    ν : Scoped (suc n) → ⦃ name : Name ⦄ → Scoped n
    _∥_   : Scoped n → Scoped n → Scoped n
    _⦅⦆_ : Fin n → Scoped (suc n) → ⦃ name : Name ⦄ → Scoped n
    _⟨_⟩_ : Fin n → Fin n → Scoped n → Scoped n

module Conversion where
  private
    open Raw
    open Scoped

    open import Level using (Lift; _⊔_)
    open import Function using (_∘_)
    open import Relation.Nullary using (Dec; yes; no)
    open import Relation.Nullary.Decidable using (isYes; True; toWitness)
    open import Relation.Nullary.Product using (_×-dec_)
    open import Relation.Nullary.Negation using (¬?)

    import Data.Vec.Base as Vec
    import Data.Char.Base as Char
    import Data.Char.Properties as Charₚ
    import Data.List.Base as List
    import Data.List.Properties as Listₚ
    import Data.String.Base as String
    import Data.String.Properties as Stringₚ
    import Data.Nat.Show as ℕₛ
    import Data.Vec.Membership.DecPropositional as DecPropositional

    open import Data.Empty using (⊥)
    open import Data.Bool.Base using (true; false; if_then_else_)
    open import Data.Product using (_,_; _×_)
    open import Data.Unit using (⊤; tt)
    open import Data.Nat.Base using (ℕ; zero; suc)
    open import Data.Fin.Base using (Fin; zero; suc)
    open import Data.String.Base using (_++_)
    open import Data.Vec.Membership.Propositional using (_∈_; _∉_)
    open import Data.Vec.Relation.Unary.Any using (here; there)

    open Vec using (Vec; []; _∷_)

    _∈?_ = DecPropositional._∈?_ (Listₚ.≡-dec Charₚ._≟_)

    variable
      n m : ℕ

  Ctx : ℕ → Set
  Ctx = Vec Name

  count : Name → Ctx n → ℕ
  count name = Vec.count (Listₚ.≡-dec Charₚ._≟_ name)

  toChars : Name × ℕ → List Char.Char
  toChars (x , i) = x List.++ ('^' ∷ ℕₛ.charsInBase 10 i)

  repr : ∀ x (xs : Vec Name n) → Name
  repr x xs = toChars (x , (count x xs))

  apply : Ctx n → Ctx n
  apply [] = []
  apply (x ∷ xs) = repr x xs ∷ apply xs

  WellScoped : Ctx n → Raw → Set
  WellScoped ctx 𝟘 = ⊤
  WellScoped ctx (⦅ν x ⦆ P) = WellScoped (x ∷ ctx) P
  WellScoped ctx (P ∥ Q) = WellScoped ctx P × WellScoped ctx Q
  WellScoped ctx (x ⦅ y ⦆ P) = (x ∈ ctx) × WellScoped (y ∷ ctx) P
  WellScoped ctx (x ⟨ y ⟩ P) = (x ∈ ctx) × (y ∈ ctx) × WellScoped ctx P

  WellScoped? : (ctx : Ctx n) (P : Raw) → Dec (WellScoped ctx P)
  WellScoped? ctx 𝟘 = yes tt
  WellScoped? ctx (⦅ν x ⦆ P) = WellScoped? (x ∷ ctx) P
  WellScoped? ctx (P ∥ Q) = WellScoped? ctx P ×-dec WellScoped? ctx Q
  WellScoped? ctx (x ⦅ y ⦆ P) = x ∈? ctx ×-dec WellScoped? (y ∷ ctx) P
  WellScoped? ctx (x ⟨ y ⟩ P) = x ∈? ctx ×-dec y ∈? ctx ×-dec WellScoped? ctx P

  NotShadowed : Ctx n → Raw → Set
  NotShadowed ctx 𝟘 = ⊤
  NotShadowed ctx (⦅ν name ⦆ P) = name ∉ ctx × NotShadowed (name ∷ ctx) P
  NotShadowed ctx (P ∥ Q) = NotShadowed ctx P × NotShadowed ctx Q
  NotShadowed ctx (x ⦅ y ⦆ P) = y ∉ ctx × NotShadowed (y ∷ ctx) P
  NotShadowed ctx (x ⟨ y ⟩ P) = NotShadowed ctx P

  NotShadowed? : (ctx : Ctx n) (P : Raw) → Dec (NotShadowed ctx P)
  NotShadowed? ctx 𝟘 = yes tt
  NotShadowed? ctx (⦅ν name ⦆ P) = ¬? (name ∈? ctx) ×-dec NotShadowed? (name ∷ ctx) P
  NotShadowed? ctx (P ∥ Q) = NotShadowed? ctx P ×-dec NotShadowed? ctx Q
  NotShadowed? ctx (x ⦅ y ⦆ P) = ¬? (y ∈? ctx) ×-dec NotShadowed? (y ∷ ctx) P
  NotShadowed? ctx (x ⟨ y ⟩ P) = NotShadowed? ctx P

  ∈toFin : ∀ {a} {A : Set a} {x} {xs : Vec A n} → x ∈ xs → Fin n
  ∈toFin (here px) = zero
  ∈toFin (there x∈xs) = suc (∈toFin x∈xs)

  fromRaw' : (ctx : Ctx n) (P : Raw) → WellScoped ctx P → Scoped n
  fromRaw' ctx 𝟘 tt = 𝟘
  fromRaw' ctx (⦅ν x ⦆ P) wsP =
    ν (fromRaw' (x ∷ ctx) P wsP) ⦃ x ⦄
  fromRaw' ctx (P ∥ Q) (wsP , wsQ) =
    fromRaw' ctx P wsP ∥ fromRaw' ctx Q wsQ
  fromRaw' ctx (x ⦅ y ⦆ P) (x∈ctx , wsP) =
    (∈toFin x∈ctx ⦅⦆ fromRaw' (y ∷ ctx) P wsP) ⦃ y ⦄
  fromRaw' ctx (x ⟨ y ⟩ P) (x∈ctx , y∈ctx , wsP) =
    ∈toFin x∈ctx ⟨ ∈toFin y∈ctx ⟩ fromRaw' ctx P wsP

  fromRaw : (ctx : Ctx n) (P : Raw) → ⦃ _ : True (WellScoped? ctx P) ⦄ → Scoped n
  fromRaw ctx P ⦃ p ⦄ = fromRaw' ctx P (toWitness p)

  toRaw : Ctx n → Scoped n → Raw
  toRaw ctx 𝟘 = 𝟘
  toRaw ctx (ν P ⦃ name ⦄) =
    ⦅ν repr name ctx ⦆ toRaw (name ∷ ctx) P
  toRaw ctx (P ∥ Q) =
    toRaw ctx P ∥ toRaw ctx Q
  toRaw ctx ((x ⦅⦆ P) ⦃ name ⦄) =
    let ctx' = apply ctx
    in Vec.lookup ctx' x ⦅ repr name ctx ⦆ toRaw (name ∷ ctx) P
  toRaw ctx (x ⟨ y ⟩ P) =
    let ctx' = apply ctx
    in Vec.lookup ctx' x ⟨ Vec.lookup ctx' y ⟩ toRaw ctx P

  map : ∀ {a} (B : Scoped n → Set a) (ctx : Vec Name n) (P : Raw) → Set a
  map B ctx P with WellScoped? ctx P
  map B ctx P | yes wsP = B (fromRaw' ctx P wsP)
  map B ctx P | no _ = Lift _ ⊥

  map₂ : ∀ {a} (B : Scoped n → Scoped n → Set a) (ctx : Vec Name n) (P Q : Raw) → Set a
  map₂ B ctx P Q with WellScoped? ctx P | WellScoped? ctx Q
  map₂ B ctx P Q | yes wsP | yes wsQ = B (fromRaw' ctx P wsP) (fromRaw' ctx Q wsQ)
  map₂ B ctx P Q | _       | _       = Lift _ ⊥
