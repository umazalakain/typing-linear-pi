{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (subst)

open import Data.Vec.Base as Vec using (Vec; []; _∷_; map; lookup; _++_; sum; length)
open import Data.String.Base using (String)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin; zero; suc)
import Data.Nat.Properties as ℕₚ

module PiCalculus.Syntax where

Name : Set
Name = String

private
  variable
    n m : ℕ

module Raw where
  infixr 20 _∥_
  infixr 15 ⦅ν_⦆_
  infixr 10 _⦅_⦆_ _⟨_⟩_

  data Raw : Set where
    𝟘     : Raw
    ⦅ν_⦆_ : Name → Raw → Raw
    _∥_   : Raw → Raw → Raw
    _⦅_⦆_ : Name → Vec Name n → Raw → Raw
    _⟨_⟩_ : Name → Vec Name n → Raw → Raw


module Scoped where

  infixr 20 _∥_
  infixr 15 ν
  infixr 10 _⦅_⦆_ _⟨_⟩_

  data Scoped : ℕ → Set where
    𝟘     : Scoped n
    ν     : Scoped (suc n) → ⦃ name : Name ⦄ → Scoped n
    _∥_   : Scoped n → Scoped n → Scoped n
    _⦅_⦆_ : Fin n → (m : ℕ) → Scoped (m + n) → ⦃ names : Vec Name m ⦄ → Scoped n
    _⟨_⟩_ : Fin n → Vec (Fin n) m → Scoped n → Scoped n

module Conversion where
  private
    open Raw
    open Scoped

    open import Level using (Lift; _⊔_)
    open import Function using (_∘_)
    open import Relation.Nullary using (¬_; Dec; yes; no)
    open import Relation.Nullary.Decidable using (isYes; True; toWitness)
    open import Relation.Nullary.Product using (_×-dec_)
    open import Relation.Nullary.Negation using (¬?)

    import Data.Char.Base as Char
    import Data.List.Base as List
    import Data.String.Base as String
    import Data.String.Properties as Stringₚ
    import Data.Vec.Membership.DecPropositional as DecPropositional

    open import Data.Empty using (⊥)
    open import Data.Bool.Base using (true; false; if_then_else_)
    open import Data.Product using (_,_; _×_)
    open import Data.Unit using (⊤; tt)
    open import Data.Vec.Membership.Propositional using (_∈_; _∉_)
    open import Data.Vec.Relation.Unary.Any as Any using (here; there)
    open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)

    open List using (List; []; _∷_)

    import PiCalculus.Utils
    module ℕₛ = PiCalculus.Utils.ℕₛ
    open PiCalculus.Utils.All2Vec

    _∈?_ = DecPropositional._∈?_ Stringₚ._≟_

  Ctx : ℕ → Set
  Ctx = Vec Name

  count : Name → Ctx n → ℕ
  count name = sum ∘ map ((if_then 1 else 0) ∘ isYes ∘ (Stringₚ._≟ name))
  -- TODO: rewrite to the following and make proofs work
  -- count name = Vec.count (Stringₚ._≟ name)

  toCharList : Name × ℕ → List Char.Char
  toCharList (x , i) = String.toList x List.++ ('^' ∷ ℕₛ.toDigitChars 10 i)

  toString : Name × ℕ → Name
  toString = String.fromList ∘ toCharList

  repr : ∀ x (xs : Vec Name n) → Name
  repr x xs = toString (x , (count x xs))

  apply-++ : ∀ (xs : Vec Name n) (ys : Vec Name m) → Vec Name n
  apply-++ [] ys = []
  apply-++ (x ∷ xs) ys = repr x (xs ++ ys) ∷ apply-++ xs ys

  apply : Ctx n → Ctx n
  apply [] = []
  apply (x ∷ xs) = repr x xs ∷ apply xs

  WellScoped : Ctx n → Raw → Set
  WellScoped ctx 𝟘 = ⊤
  WellScoped ctx (⦅ν x ⦆ P) = WellScoped (x ∷ ctx) P
  WellScoped ctx (P ∥ Q) = WellScoped ctx P × WellScoped ctx Q
  WellScoped ctx (x ⦅ ys ⦆ P) = (x ∈ ctx) × WellScoped (ys ++ ctx) P
  WellScoped ctx (x ⟨ ys ⟩ P) = (x ∈ ctx) × All (_∈ ctx) ys × WellScoped ctx P

  WellScoped? : (ctx : Ctx n) (P : Raw) → Dec (WellScoped ctx P)
  WellScoped? ctx 𝟘 = yes tt
  WellScoped? ctx (⦅ν x ⦆ P) = WellScoped? (x ∷ ctx) P
  WellScoped? ctx (P ∥ Q) = WellScoped? ctx P ×-dec WellScoped? ctx Q
  WellScoped? ctx (x ⦅ ys ⦆ P) = x ∈? ctx ×-dec WellScoped? (ys ++ ctx) P
  WellScoped? ctx (x ⟨ ys ⟩ P) = x ∈? ctx ×-dec All.all (_∈? ctx) ys ×-dec WellScoped? ctx P

  NotShadowed : Ctx n → Raw → Set
  NotShadowed ctx 𝟘 = ⊤
  NotShadowed ctx (⦅ν name ⦆ P) = name ∉ ctx × NotShadowed (name ∷ ctx) P
  NotShadowed ctx (P ∥ Q) = NotShadowed ctx P × NotShadowed ctx Q
  NotShadowed ctx (x ⦅ ys ⦆ P) = All (_∉ ctx) ys × NotShadowed (ys ++ ctx) P
  NotShadowed ctx (x ⟨ ys ⟩ P) = NotShadowed ctx P

  NotShadowed? : (ctx : Ctx n) (P : Raw) → Dec (NotShadowed ctx P)
  NotShadowed? ctx 𝟘 = yes tt
  NotShadowed? ctx (⦅ν name ⦆ P) = ¬? (name ∈? ctx) ×-dec NotShadowed? (name ∷ ctx) P
  NotShadowed? ctx (P ∥ Q) = NotShadowed? ctx P ×-dec NotShadowed? ctx Q
  NotShadowed? ctx (x ⦅ ys ⦆ P) = All.all (¬? ∘ _∈? ctx) ys ×-dec NotShadowed? (ys ++ ctx) P
  NotShadowed? ctx (x ⟨ ys ⟩ P) = NotShadowed? ctx P

  fromRaw' : (ctx : Ctx n) (P : Raw) → WellScoped ctx P → Scoped n
  fromRaw' ctx 𝟘 tt = 𝟘
  fromRaw' ctx (⦅ν x ⦆ P) wsP =
    ν (fromRaw' (x ∷ ctx) P wsP) ⦃ x ⦄
  fromRaw' ctx (P ∥ Q) (wsP , wsQ) =
    fromRaw' ctx P wsP ∥ fromRaw' ctx Q wsQ
  fromRaw' {n = n} ctx (x ⦅ ys ⦆ P) (x∈ctx , wsP) =
    (Any.index x∈ctx ⦅ length ys ⦆ fromRaw' (ys ++ ctx) P wsP) ⦃ ys ⦄
  fromRaw' ctx (x ⟨ ys ⟩ P) (x∈ctx , ys∈ctx , wsP) =
    Any.index x∈ctx ⟨  all2vec Any.index ys∈ctx  ⟩ fromRaw' ctx P wsP

  fromRaw : (ctx : Ctx n) (P : Raw) → ⦃ _ : True (WellScoped? ctx P) ⦄ → Scoped n
  fromRaw ctx P ⦃ p ⦄ = fromRaw' ctx P (toWitness p)

  toRaw : Ctx n → Scoped n → Raw
  toRaw ctx 𝟘 = 𝟘
  toRaw ctx (ν P ⦃ name ⦄) =
    ⦅ν repr name ctx ⦆ toRaw (name ∷ ctx) P
  toRaw ctx (P ∥ Q) =
    toRaw ctx P ∥ toRaw ctx Q
  toRaw {n = n} ctx ((x ⦅ m ⦆ P) ⦃ names ⦄) =
    let ctx' = apply ctx
    in lookup ctx' x ⦅ apply-++ names ctx ⦆ toRaw (names ++ ctx) P
  toRaw ctx (x ⟨ ys ⟩ P) =
    let ctx' = apply ctx
    in lookup ctx' x ⟨ map (lookup ctx') ys ⟩ toRaw ctx P

  fmap : ∀ {a} (B : Scoped n → Set a) (ctx : Vec Name n) (P : Raw) → Set a
  fmap B ctx P with WellScoped? ctx P
  fmap B ctx P | yes wsP = B (fromRaw' ctx P wsP)
  fmap B ctx P | no _ = Lift _ ⊥

  fmap₂ : ∀ {a} (B : Scoped n → Scoped n → Set a) (ctx : Vec Name n) (P Q : Raw) → Set a
  fmap₂ B ctx P Q with WellScoped? ctx P | WellScoped? ctx Q
  fmap₂ B ctx P Q | yes wsP | yes wsQ = B (fromRaw' ctx P wsP) (fromRaw' ctx Q wsQ)
  fmap₂ B ctx P Q | _       | _       = Lift _ ⊥
