{-# OPTIONS --safe #-} -- --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (fromWitness)

import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Nat as ℕ
import Data.Vec as Vec
import Data.Fin as Fin
import Data.Vec.Relation.Unary.All as All

open Unit using (⊤; tt)
open ℕ using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Syntax
open Scoped
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem.Algebras


module PiCalculus.LinearTypeSystem.SubjectCongruence (Ω : Algebras) where
open Algebras Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem.Framing Ω
open import PiCalculus.LinearTypeSystem.Weakening Ω
open import PiCalculus.LinearTypeSystem.Strengthening Ω
open import PiCalculus.LinearTypeSystem.Exchange Ω

SubjectCongruence : Set
SubjectCongruence = {n : ℕ} {γ : PreCtx n} {idxs : Idxs n} {Γ Δ : Ctx idxs}
                  → {r : RecTree} {P Q : Scoped n}
                  → P ≅⟨ r ⟩ Q
                  → γ ； Γ ⊢ P ▹ Δ
                  → γ ； Γ ⊢ Q ▹ Δ

private
  variable
    n : ℕ
    P Q : Scoped n

comp-comm : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs}
          → γ ； Γ ⊢ P ∥ Q ▹ Ξ
          → γ ； Γ ⊢ Q ∥ P ▹ Ξ
comp-comm (⊢P ∥ ⊢Q) with ⊢-⊗ ⊢P | ⊢-⊗ ⊢Q
comp-comm (⊢P ∥ ⊢Q) | _ , P≔ | _ , Q≔ =
  let _ , (Q'≔ , P'≔) = ⊗-assoc (⊗-comm P≔) Q≔ in
  ⊢-frame Q≔ Q'≔ ⊢Q ∥ ⊢-frame P≔ (⊗-comm P'≔) ⊢P

subject-cong : SubjectCongruence
subject-cong (stop comp-assoc) (⊢P ∥ (⊢Q ∥ ⊢R)) = (⊢P ∥ ⊢Q) ∥ ⊢R
subject-cong (stop comp-symm) (⊢P ∥ ⊢Q) = comp-comm (⊢P ∥ ⊢Q)
subject-cong (stop comp-end) (⊢P ∥ 𝟘) = ⊢P
subject-cong (stop scope-end) (ν t c ._ 𝟘) = 𝟘
subject-cong (stop (scope-ext u)) (ν t c μ (_∥_ {Δ = _ -, _} ⊢P ⊢Q)) rewrite sym (⊢-unused _ u ⊢P) = ⊢-strengthen zero u ⊢P ∥ ν t c μ ⊢Q
subject-cong (stop scope-scope-comm) (ν t c μ (ν t₁ c₁ μ₁ ⊢P)) = ν t₁ c₁ μ₁ (ν t c μ (⊢-exchange zero ⊢P))
subject-cong (cong-symm (stop comp-assoc)) ((⊢P ∥ ⊢Q) ∥ ⊢R) = ⊢P ∥ (⊢Q ∥ ⊢R)
subject-cong (cong-symm (stop comp-symm)) (⊢P ∥ ⊢Q) = comp-comm (⊢P ∥ ⊢Q)
subject-cong (cong-symm (stop comp-end)) ⊢P = ⊢P ∥ 𝟘
subject-cong (cong-symm (stop scope-end)) 𝟘 = ν 𝟙 {∃Idx} (0∙ , 0∙) {∃Idx} 0∙ 𝟘
subject-cong (cong-symm (stop (scope-ext u))) (⊢P ∥ (ν t c μ ⊢Q)) = ν t c μ ((subst (λ ● → _ ； _ ⊢ ● ▹ _) (lift-lower zero _ u) (⊢-weaken zero ⊢P)) ∥ ⊢Q)
subject-cong (cong-symm (stop scope-scope-comm)) (ν t c μ (ν t₁ c₁ μ₁ ⊢P)) = ν _ _ _ (ν _ _ _ (subst (λ ● → _ ； _ ⊢ ● ▹ _) (exchange-exchange zero _) (⊢-exchange zero ⊢P)))

-- Equivalence and congruence
subject-cong cong-refl ⊢P = ⊢P
subject-cong (cong-trans P≅Q Q≅R) ⊢P = subject-cong Q≅R (subject-cong P≅Q ⊢P)
subject-cong (ν-cong P≅Q) (ν t m μ ⊢P) = ν t m μ (subject-cong P≅Q ⊢P)
subject-cong (comp-cong P≅Q) (⊢P ∥ ⊢R) = subject-cong P≅Q ⊢P ∥ ⊢R
subject-cong (input-cong P≅Q) (x ⦅⦆ ⊢P) = x ⦅⦆ subject-cong P≅Q ⊢P
subject-cong (output-cong P≅Q) (x ⟨ y ⟩ ⊢P) = x ⟨ y ⟩ subject-cong P≅Q ⊢P
subject-cong (cong-symm cong-refl) ⊢P = ⊢P
subject-cong (cong-symm (cong-symm P≅Q)) ⊢P = subject-cong P≅Q ⊢P
subject-cong (cong-symm cong-trans P≅Q P≅R) ⊢P = subject-cong (cong-symm P≅Q) (subject-cong (cong-symm P≅R) ⊢P)
subject-cong (cong-symm (ν-cong P≅Q)) (ν t m μ ⊢P) = ν t m μ (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (comp-cong P≅Q)) (⊢P ∥ ⊢R) = subject-cong (cong-symm P≅Q) ⊢P ∥ ⊢R
subject-cong (cong-symm (input-cong P≅Q)) (x ⦅⦆ ⊢P) = x ⦅⦆ subject-cong (cong-symm P≅Q) ⊢P
subject-cong (cong-symm (output-cong P≅Q)) (x ⟨ y ⟩ ⊢P) = x ⟨ y ⟩ subject-cong (cong-symm P≅Q) ⊢P
