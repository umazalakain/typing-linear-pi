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

module PiCalculus.LinearTypeSystem.Swapping (Ω : Algebras) where
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
  swapᵥ : (i : Fin n) → Vec A (suc n) → Vec A (suc n)
  swapᵥ zero (xs -, y -, x) = xs -, x -, y
  swapᵥ (suc i) (xs -, y -, x) = swapᵥ i (xs -, y) -, x

  swapₐ : ∀ {b} {P : A → Set b} (i : Fin n) {xs : Vec A (suc n)} → All P xs → All P (swapᵥ i xs)
  swapₐ zero (xs -, y -, x) = xs -, x -, y
  swapₐ (suc i) (xs -, y -, x) = swapₐ i (xs -, y) -, x

-- TODO: rewrite this crap
∋-swap : {γ : PreCtx (suc n)} {idxs : Idxs (suc n)} {Γ Θ : Ctx idxs} {t : Type} {x : Usage idx ²}
       → (i : Fin n)
       → γ ； Γ ∋[ j ] t ； x ▹ Θ
       → swapᵥ i γ ； swapₐ i Γ ∋[ swapFin i j ] t ； x ▹ swapₐ i Θ
∋-swap {γ = _ -, _ -, _} {idxs = _ -, _ -, _} {Γ = _ -, _ -, _} zero (zero , zero xyz) = (suc zero , suc (zero xyz))
∋-swap {γ = _ -, _ -, _} zero (suc zero , suc (zero xyz)) = zero , zero xyz
∋-swap {γ = _ -, _ -, _} zero (suc (suc t) , suc (suc x)) = suc (suc t) , suc (suc x)
∋-swap {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (zero , zero xyz) = zero , zero xyz
∋-swap {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc zero) (suc zero , suc (zero xyz)) = suc (suc zero) , suc (suc (zero xyz))
∋-swap {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc (suc i)) (suc zero , suc (zero xyz)) = suc zero , suc (zero xyz)
∋-swap {j = suc (suc j)} {γ = γ -, _} {Γ = Γ -, _} (suc i) (suc (suc t) , suc (suc x)) with Fin.inject₁ i Finₚ.≟ suc j
∋-swap {j = suc (suc j)} {γ = γ -, _} {Γ = Γ -, _} (suc zero) (suc (suc t) , suc (suc x)) | yes ()
∋-swap {j = suc (suc ._)} {γ = γ -, _} {Γ = Γ -, _} {Θ = Θ -, _} (suc (suc i)) (suc st@(suc t) , suc sx@(suc x)) | yes refl =
  let s' = subst (λ ● → swapᵥ (suc i) γ ； swapₐ (suc i) Γ ∋[ ● ] _ ； _ ▹ swapₐ (suc i) Θ)
                 (sym (trans (cong suc (sym (trans (swapFin-injectˡ i) (cong suc (sym (Finₚ.lower₁-inject₁′ i _))))))
                 (swapFin-suc i (Fin.inject₁ i)))) (∋-swap (suc i) (st , sx))
  in there s'
∋-swap {j = suc (suc j)} {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (suc st@(suc t) , suc sx@(suc x)) | no ¬p with i Finₚ.≟ j
∋-swap {j = suc (suc j)} {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (suc st@(suc t) , suc sx@(suc x)) | no ¬p | yes refl rewrite sym (swapFin-injectʳ i) = there (∋-swap i (st , sx))
∋-swap {j = suc (suc j)} {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (suc st@(suc t) , suc sx@(suc x)) | no ¬p | no ¬q rewrite sym (swapFin-neq i j ¬q ¬p) = there (∋-swap i (st , sx))

⊢-swap : {γ : PreCtx (suc n)} {Γ Θ : Ctx idxs}
       → (i : Fin n)
       → γ ； Γ ⊢ P ▹ Θ
       → swapᵥ i γ ； swapₐ i Γ ⊢ swap i P ▹ swapₐ i Θ
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i 𝟘 = 𝟘
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (ν t m μ ⊢P) = ν t m μ (⊢-swap (suc i) ⊢P)
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (_⦅⦆_ {Ξ = _ -, _ -, _} x ⊢P) = ∋-swap i x ⦅⦆ ⊢-swap (suc i) ⊢P
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (x ⟨ y ⟩ ⊢P) = ∋-swap i x ⟨ ∋-swap i y ⟩ (⊢-swap i ⊢P)
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (⊢P ∥ ⊢Q) = ⊢-swap i ⊢P ∥ ⊢-swap i ⊢Q
