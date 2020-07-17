{-# OPTIONS --safe #-} -- --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl; sym; subst; cong; trans)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

import Data.Empty as Empty
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Fin as Fin
import Data.Fin.Properties as Finₚ
import Data.Vec.Relation.Unary.All as All

open Empty using (⊥-elim)
open Nat using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

import PiCalculus.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem.Algebras

module PiCalculus.LinearTypeSystem.Exchange (Ω : Algebras) where
open Algebras Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    i j : Fin n
    idx : Idx
    idxs : Idxs n
    P Q : Scoped n

⊢-unused : {γ : PreCtx n} {Γ Θ : Ctx idxs}
         → (i : Fin n)
         → Unused i P
         → γ ； Γ ⊢ P ▹ Θ
         → All.lookup i Γ ≡ All.lookup i Θ
⊢-unused i uP 𝟘 = refl
⊢-unused i uP (ν t m μ ⊢P) = ⊢-unused (suc i) uP ⊢P
⊢-unused i (i≢x , uP) ((_ , x) ⦅⦆ ⊢P) = trans
  (∋-lookup-≢ x i i≢x)
  (⊢-unused (suc i) uP ⊢P)
⊢-unused i (i≢x , i≢y , uP) ((_ , x) ⟨ _ , y ⟩ ⊢P) = trans (trans
  (∋-lookup-≢ x i i≢x)
  (∋-lookup-≢ y i i≢y))
  (⊢-unused i uP ⊢P)
⊢-unused i (uP , uQ) (⊢P ∥ ⊢Q) = trans
  (⊢-unused i uP ⊢P)
  (⊢-unused i uQ ⊢Q)

module _ {a} {A : Set a} where
  exchangeᵥ : (i : Fin n) → Vec A (suc n) → Vec A (suc n)
  exchangeᵥ zero (xs -, y -, x) = xs -, x -, y
  exchangeᵥ (suc i) (xs -, y -, x) = exchangeᵥ i (xs -, y) -, x

  exchangeₐ : ∀ {b} {P : A → Set b} (i : Fin n) {xs : Vec A (suc n)} → All P xs → All P (exchangeᵥ i xs)
  exchangeₐ zero (xs -, y -, x) = xs -, x -, y
  exchangeₐ (suc i) (xs -, y -, x) = exchangeₐ i (xs -, y) -, x

-- TODO: rewrite this crap
∋-exchange : {γ : PreCtx (suc n)} {idxs : Idxs (suc n)} {Γ Θ : Ctx idxs} {t : Type} {x : Usage idx ²}
       → (i : Fin n)
       → γ ； Γ ∋[ j ] t ； x ▹ Θ
       → exchangeᵥ i γ ； exchangeₐ i Γ ∋[ exchangeFin i j ] t ； x ▹ exchangeₐ i Θ
∋-exchange {γ = _ -, _ -, _} {idxs = _ -, _ -, _} {Γ = _ -, _ -, _} zero (zero , zero xyz) = (suc zero , suc (zero xyz))
∋-exchange {γ = _ -, _ -, _} zero (suc zero , suc (zero xyz)) = zero , zero xyz
∋-exchange {γ = _ -, _ -, _} zero (suc (suc t) , suc (suc x)) = suc (suc t) , suc (suc x)
∋-exchange {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (zero , zero xyz) = zero , zero xyz
∋-exchange {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc zero) (suc zero , suc (zero xyz)) = suc (suc zero) , suc (suc (zero xyz))
∋-exchange {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc (suc i)) (suc zero , suc (zero xyz)) = suc zero , suc (zero xyz)
∋-exchange {j = suc (suc j)} {γ = γ -, _} {Γ = Γ -, _} (suc i) (suc (suc t) , suc (suc x)) with Fin.inject₁ i Finₚ.≟ suc j
∋-exchange {j = suc (suc j)} {γ = γ -, _} {Γ = Γ -, _} (suc zero) (suc (suc t) , suc (suc x)) | yes ()
∋-exchange {j = suc (suc ._)} {γ = γ -, _} {Γ = Γ -, _} {Θ = Θ -, _} (suc (suc i)) (suc st@(suc t) , suc sx@(suc x)) | yes refl =
  let s' = subst (λ ● → exchangeᵥ (suc i) γ ； exchangeₐ (suc i) Γ ∋[ ● ] _ ； _ ▹ exchangeₐ (suc i) Θ)
                 (sym (trans (cong suc (sym (trans (exchangeFin-injectˡ i) (cong suc (sym (Finₚ.lower₁-inject₁′ i _))))))
                 (exchangeFin-suc i (Fin.inject₁ i)))) (∋-exchange (suc i) (st , sx))
  in there s'
∋-exchange {j = suc (suc j)} {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (suc st@(suc t) , suc sx@(suc x)) | no ¬p with i Finₚ.≟ j
∋-exchange {j = suc (suc j)} {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (suc st@(suc t) , suc sx@(suc x)) | no ¬p | yes refl rewrite sym (exchangeFin-injectʳ i) = there (∋-exchange i (st , sx))
∋-exchange {j = suc (suc j)} {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (suc st@(suc t) , suc sx@(suc x)) | no ¬p | no ¬q rewrite sym (exchangeFin-neq i j ¬q ¬p) = there (∋-exchange i (st , sx))

⊢-exchange : {γ : PreCtx (suc n)} {Γ Θ : Ctx idxs}
       → (i : Fin n)
       → γ ； Γ ⊢ P ▹ Θ
       → exchangeᵥ i γ ； exchangeₐ i Γ ⊢ exchange i P ▹ exchangeₐ i Θ
⊢-exchange {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i 𝟘 = 𝟘
⊢-exchange {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (ν t m μ ⊢P) = ν t m μ (⊢-exchange (suc i) ⊢P)
⊢-exchange {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (_⦅⦆_ {Ξ = _ -, _ -, _} x ⊢P) = ∋-exchange i x ⦅⦆ ⊢-exchange (suc i) ⊢P
⊢-exchange {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (x ⟨ y ⟩ ⊢P) = ∋-exchange i x ⟨ ∋-exchange i y ⟩ (⊢-exchange i ⊢P)
⊢-exchange {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (⊢P ∥ ⊢Q) = ⊢-exchange i ⊢P ∥ ⊢-exchange i ⊢Q
