open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (yes; no)

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

open import PiCalculus.Function
open import PiCalculus.Syntax
open Scoped
open Syntax
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem.Quantifiers


module PiCalculus.LinearTypeSystem.SubjectCongruence (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem.Framing Ω
open import PiCalculus.LinearTypeSystem.Weakening Ω
open import PiCalculus.LinearTypeSystem.Strengthening Ω
open import PiCalculus.LinearTypeSystem.Swapping Ω

SubjectCongruence : Set
SubjectCongruence = {n : ℕ} {γ : PreCtx n} {is : Vec I n} {Γ Δ : Ctx is}
                  → {r : RecTree} {P Q : Scoped n}
                  → P ≅⟨ r ⟩ Q
                  → γ ∝ Γ ⊢ P ⊠ Δ
                  → γ ∝ Γ ⊢ Q ⊠ Δ

private
  variable
    n : ℕ
    P Q : Scoped n

comp-comm : {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ : Ctx idxs}
          → γ ∝ Γ ⊢ P ∥ Q ⊠ Ξ
          → γ ∝ Γ ⊢ Q ∥ P ⊠ Ξ
comp-comm (comp ⊢P ⊢Q) with ⊢-⊎ ⊢P | ⊢-⊎ ⊢Q
comp-comm (comp ⊢P ⊢Q) | _ , P≔ | _ , Q≔ =
  let _ , (Q'≔ , P'≔) = ⊎-assoc (⊎-comm P≔) Q≔ in
  comp (⊢-frame Q≔ Q'≔ ⊢Q) (⊢-frame P≔ (⊎-comm P'≔) ⊢P)

subject-cong : SubjectCongruence
subject-cong (stop comp-assoc) (comp ⊢P (comp ⊢Q ⊢R)) = comp (comp ⊢P ⊢Q) ⊢R
subject-cong (stop comp-symm) (comp ⊢P ⊢Q) = comp-comm (comp ⊢P ⊢Q)
subject-cong (stop comp-end) (comp ⊢P end) = ⊢P
subject-cong (stop scope-end) (chan t c ._ end) = end
subject-cong (stop (scope-ext u)) (chan t c μ (comp {Δ = _ -, _} ⊢P ⊢Q)) rewrite sym (⊢-unused _ u ⊢P) = comp (⊢-strengthen zero u ⊢P) (chan t c μ ⊢Q)
subject-cong (stop scope-scope-comm) (chan t c μ (chan t₁ c₁ μ₁ ⊢P)) = chan t₁ c₁ μ₁ (chan t c μ (⊢-swap zero ⊢P))
subject-cong (cong-symm (stop comp-assoc)) (comp (comp ⊢P ⊢Q) ⊢R) = comp ⊢P (comp ⊢Q ⊢R)
subject-cong (cong-symm (stop comp-symm)) (comp ⊢P ⊢Q) = comp-comm (comp ⊢P ⊢Q)
subject-cong (cong-symm (stop comp-end)) ⊢P = comp ⊢P end
subject-cong (cong-symm (stop scope-end)) end = chan {i' = ∃I} {i = ∃I} B[ 0 ] 0∙ 0∙ end
subject-cong (cong-symm (stop (scope-ext u))) (comp ⊢P (chan t c μ ⊢Q)) = chan t c μ (comp (subst (λ ● → _ ∝ _ ⊢ ● ⊠ _) (lift-lower zero _ u) (⊢-weaken zero ⊢P)) ⊢Q)
subject-cong (cong-symm (stop scope-scope-comm)) (chan t c μ (chan t₁ c₁ μ₁ ⊢P)) = chan _ _ _ (chan _ _ _ (subst (λ ● → _ ∝ _ ⊢ ● ⊠ _) (swap-swap zero _) (⊢-swap zero ⊢P)))

-- Equivalence and congruence
subject-cong cong-refl ⊢P = ⊢P
subject-cong (cong-trans P≅Q Q≅R) ⊢P = subject-cong Q≅R (subject-cong P≅Q ⊢P)
subject-cong (new-cong P≅Q) (chan t m μ ⊢P) = chan t m μ (subject-cong P≅Q ⊢P)
subject-cong (comp-cong P≅Q) (comp ⊢P ⊢R) = comp (subject-cong P≅Q ⊢P) ⊢R
subject-cong (input-cong P≅Q) (recv x ⊢P) = recv x (subject-cong P≅Q ⊢P)
subject-cong (output-cong P≅Q) (send x y ⊢P) = send x y (subject-cong P≅Q ⊢P)
subject-cong (cong-symm cong-refl) ⊢P = ⊢P
subject-cong (cong-symm (cong-symm P≅Q)) ⊢P = subject-cong P≅Q ⊢P
subject-cong (cong-symm cong-trans P≅Q P≅R) ⊢P = subject-cong (cong-symm P≅Q) (subject-cong (cong-symm P≅R) ⊢P)
subject-cong (cong-symm (new-cong P≅Q)) (chan t m μ ⊢P) = chan t m μ (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (comp-cong P≅Q)) (comp ⊢P ⊢R) = comp (subject-cong (cong-symm P≅Q) ⊢P) ⊢R
subject-cong (cong-symm (input-cong P≅Q)) (recv x ⊢P) = recv x (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (output-cong P≅Q)) (send x y ⊢P) = send x y (subject-cong (cong-symm P≅Q) ⊢P)
