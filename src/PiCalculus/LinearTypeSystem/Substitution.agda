open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary.Decidable using (toWitness; fromWitness)
open import Relation.Nullary using (yes; no)
open import Function.Reasoning
open import Function using (_∘_)

import Data.Empty as Empty
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Nat.Base as Nat
import Data.Vec.Base as Vec
import Data.Vec.Properties as Vecₚ
import Data.Fin.Base as Fin
import Data.Vec.Relation.Unary.All as All

open Empty using (⊥-elim)
open Unit using (tt)
open Nat using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Substitution (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    i j : Fin n
    t : Type
    γ : PreCtx n
    idx : I
    idxs : Vec I n
    x : Cs idx
    Γ Δ Δ' Θ Ψ : Ctx idxs
    P : Scoped n



data _w_[_/_]⊠_ : PreCtx n → {idxs : Vec I n} → Ctx idxs → Fin n → Fin n → Ctx idxs → Set where
  zero : (i : γ w Γ ∋ t w x ⊠ Δ)
       → γ -, t w Γ -, 0∙ [ suc (toFin i) / zero  ]⊠ Δ -, x
  suc  : γ w Γ [ i / j ]⊠ Δ
       → γ -, t w Γ -, x  [ suc i         / suc j ]⊠ Δ -, x


foo : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ Ψ : Ctx idxs}
    → {i j : Fin n}
    → γ w Γ ⊢ P ⊠ Ψ
    → γ w Ψ [ j / i ]⊠ Ξ
    → γ w Γ ⊢ [ j / i ] P ⊠ Ξ
foo end xy = {!!}
foo (chan t m μ ⊢P) xy = chan t m μ (foo ⊢P (suc xy))
foo (recv x ⊢P) xy = {!x!}
foo (send x y ⊢P) xy = {!!}
foo (comp ⊢P ⊢Q) xy = {!!}

⊢-subst' : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Cs idx}
         → γ -, t w Γ -, m ⊢ P ⊠ Ψ -, 0∙
         → (y : γ w Ψ ∋ t w m ⊠ Ξ)
         → γ -, t w Γ -, m ⊢ [ suc (toFin y) / zero ] P ⊠ Ξ -, m
⊢-subst' ⊢P y = foo ⊢P (zero y)

{- TARGET -}
⊢-subst : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ Ψ : Ctx idxs} {t t'} {idx idx'}  {m : Cs idx} {m' : Cs idx'}
        → γ -, t' w Γ -, m' ⊢ P ⊠ Ψ -, 0∙
        → (y : γ w Ψ ∋ t w m ⊠ Ξ)
        → γ -, t' w Γ -, m' ⊢ [ suc (toFin y) / zero ] P ⊠ Ξ -, m'
