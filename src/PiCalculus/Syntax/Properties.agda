{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using ([]; _∷_; Vec; lookup)
open import Data.String.Base using (String)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing; _>>=_; maybe)
open import Data.Vec.Relation.Unary.Any using (here; there; index)
open import Data.Vec.Membership.Propositional using (_∈_; _∉_)
import Data.Vec.Relation.Unary.Any.Properties as Anyₚ
import Data.Vec.Membership.Propositional.Properties as ∈ₚ

open import PiCalculus.Syntax
open Raw
open Scoped
open Conversion

module PiCalculus.Syntax.Properties where

private
  variable
    n : ℕ
    P Q R S : Scoped n
    namex namey : String

toRaw-WellScoped : (ctx : Vec String n) (P : Scoped n) → WellScoped ctx (toRaw ctx P)
toRaw-WellScoped ctx 𝟘 = tt
toRaw-WellScoped ctx (υ P ⦃ name ⦄) =
  toRaw-WellScoped (fresh ctx name ∷ ctx) P
toRaw-WellScoped ctx (P ∥ Q) =
  toRaw-WellScoped ctx P , toRaw-WellScoped ctx Q
toRaw-WellScoped ctx ((x ⦅⦆ P) ⦃ name ⦄) =
  ∈ₚ.∈-lookup x ctx , (toRaw-WellScoped (fresh ctx name ∷ ctx) P)
toRaw-WellScoped ctx (x ⟨ y ⟩ P) =
  ∈ₚ.∈-lookup x ctx , ∈ₚ.∈-lookup y ctx , toRaw-WellScoped ctx P

fromName∘toName : (i : Fin n) (ctx : Vec String n) → ∈toFin (∈ₚ.∈-lookup i ctx) ≡ i
fromName∘toName zero (x ∷ ctx) = refl
fromName∘toName (suc i) (x ∷ ctx) rewrite fromName∘toName i ctx = refl

toName∘fromName : ∀ {x} {ctx : Vec String n} (x∈ctx : x ∈ ctx) → lookup ctx (∈toFin x∈ctx) ≡ x
toName∘fromName (here px) = sym px
toName∘fromName (there x∈ctx) = toName∘fromName x∈ctx

data _Nameless≡_ {n} : Scoped n → Scoped n → Set where
  inaction : 𝟘 Nameless≡ 𝟘
  scope : P Nameless≡ Q → υ P ⦃ namex ⦄ Nameless≡ υ Q ⦃ namey ⦄
  comp : P Nameless≡ Q → R Nameless≡ S → (P ∥ R) Nameless≡ (Q ∥ S)
  input : ∀ {x} → P Nameless≡ Q → (x ⦅⦆ P) ⦃ namex ⦄ Nameless≡ (x ⦅⦆ Q) ⦃ namey ⦄
  output : ∀ {x y} → P Nameless≡ Q → (x ⟨ y ⟩ P) Nameless≡ (x ⟨ y ⟩ Q)

fromRaw∘toRaw : (ctx : Vec String n) (P : Scoped n)
              → fromRaw' ctx (toRaw ctx P) (toRaw-WellScoped ctx P) Nameless≡ P
fromRaw∘toRaw ctx 𝟘 = inaction
fromRaw∘toRaw ctx (υ P ⦃ name ⦄) =
  scope (fromRaw∘toRaw (fresh ctx name ∷ ctx) P)
fromRaw∘toRaw ctx (P ∥ Q) =
  comp (fromRaw∘toRaw ctx P) (fromRaw∘toRaw ctx Q)
fromRaw∘toRaw ctx ((x ⦅⦆ P) ⦃ name ⦄)
  rewrite fromName∘toName x ctx =
  input (fromRaw∘toRaw (fresh ctx name ∷ ctx) P)
fromRaw∘toRaw ctx (x ⟨ y ⟩ P)
  rewrite fromName∘toName x ctx | fromName∘toName y ctx =
  output (fromRaw∘toRaw ctx P)

∌-fresh : ∀ {name} (ctx : Vec String n) → name ∉ ctx → fresh ctx name ≡ name
∌-fresh [] name∉ctx = refl
∌-fresh (x ∷ ctx) name∉x∷ctx = ∌-fresh ctx (name∉x∷ctx ∘ there)

toRaw∘fromRaw : (ctx : Vec String n) (P : Raw)
              → NotShadowed ctx P → (wsP : WellScoped ctx P)
              → toRaw ctx (fromRaw' ctx P wsP) ≡ P

toRaw∘fromRaw ctx 𝟘 nsP wsP = refl
toRaw∘fromRaw ctx (⦅υ name ⦆ P) (name∉ctx , nsP) wsP
  rewrite ∌-fresh ctx name∉ctx | toRaw∘fromRaw (name ∷ ctx) P nsP wsP = refl
toRaw∘fromRaw ctx (P ∥ Q) (nsP , nsQ) (wsP , wsQ)
  rewrite toRaw∘fromRaw ctx P nsP wsP | toRaw∘fromRaw ctx Q nsQ wsQ = refl
toRaw∘fromRaw ctx (x ⦅ y ⦆ P) (y∉ctx , nsP) (x∈ctx , wsP)
  rewrite ∌-fresh ctx y∉ctx | toName∘fromName x∈ctx | toRaw∘fromRaw (y ∷ ctx) P nsP wsP = refl
toRaw∘fromRaw ctx (x ⟨ y ⟩ P) nsP (x∈ctx , y∈ctx , wsP)
  rewrite toName∘fromName x∈ctx | toName∘fromName y∈ctx | toRaw∘fromRaw ctx P nsP wsP = refl
