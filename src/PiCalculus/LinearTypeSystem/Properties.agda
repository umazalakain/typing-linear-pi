open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (fromWitness; toWitness)
open import Function using (_∘_)
open import Function.Reasoning

import Data.Empty as Empty
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Maybe as Maybe
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Bool as Bool
import Data.Fin as Fin
import Data.Vec.Relation.Unary.All as All
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
import Data.Fin.Properties as Finₚ

open Unit using (⊤; tt)
open Nat using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Bool using (T)
open Maybe using (nothing; just)
open Pointwise using (Pointwise; []; _∷_)
open Product using (Σ-syntax; _×_; _,_; proj₁; proj₂; uncurry)

open import PiCalculus.Function
open import PiCalculus.Syntax
open Scoped
open Syntax
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.OmegaNat
open import PiCalculus.LinearTypeSystem.Theorems
open import PiCalculus.LinearTypeSystem.ContextLemmas

module PiCalculus.LinearTypeSystem.Properties where

private
  variable
    n : ℕ
    P Q : Scoped n

∋-⊆ : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
    → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
    → γ w Γ ∋ t w m ⊠ Δ → Δ ⊆ Γ
∋-⊆ zero = (ε , _) , _,_ & ⊎-idʳ _ ⊗ refl
∋-⊆ (suc ⊢P) with ∋-⊆ ⊢P
∋-⊆ (suc ⊢P) | Γ , refl = (Γ , replicate ω0) , _,_ & refl ⊗ +ᵥ-idʳ _

⊢-⊆ : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
    → γ w Γ ⊢ P ⊠ Δ → Δ ⊆ Γ
⊢-⊆ end = ⊆-refl
⊢-⊆ (base ⊢P) = ⊆-tail {s = < 0 & _ , [] >} (⊢-⊆ ⊢P)
⊢-⊆ (chan {s = s} t m μ ⊢P) = ⊆-tail {s = < 2 & _ , s ∷ [] >} (⊢-⊆ ⊢P)
⊢-⊆ (recv {s = s} x ⊢P) = ⊆-trans (⊆-tail {s = s} (⊢-⊆ ⊢P) ) (∋-⊆ x)
⊢-⊆ (send x y ⊢P) = ⊆-trans (⊢-⊆ ⊢P) (⊆-trans (∋-⊆ y) (∋-⊆ x))
⊢-⊆ (comp ⊢P ⊢Q) = ⊆-trans (⊢-⊆ ⊢Q) (⊢-⊆ ⊢P)

--  x : (Θ ⊎ Δ₁) ⊠ (Θ ⊎ Δ₂)
-- ⊢P : (Θ ⊎ Δ₂) ⊠ Θ

∋-frame : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ Θ : Mults cs}
        → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
        → (Ξ : Mults cs)
        → Θ ⊎ Δ ≡ Γ
        → (x : γ w Γ ∋ t w m ⊠ Θ)
        → Σ[ y ∈ γ w (Ξ ⊎ Δ) ∋ t w m ⊠ Ξ ]
          toFin x ≡ toFin y
∋-frame {Δ = Δ , l} (Ξ , n) eq zero
  rewrite ⊎-cancelˡ-≡ (trans (Productₚ.,-injectiveˡ eq) (sym (⊎-idʳ _)))
        | ⊎-idʳ Ξ
        | +ᵥ-cancelˡ-≡ (Productₚ.,-injectiveʳ eq)
        = zero , refl
∋-frame (Ξ , m) eq (suc x) with ∋-frame Ξ (Productₚ.,-injectiveˡ eq) x
∋-frame (Ξ , m) eq (suc x) | x' , p'
  rewrite +ᵥ-cancelˡ-≡ (trans (Productₚ.,-injectiveʳ eq) (sym (+ᵥ-idʳ _)))
        | +ᵥ-idʳ m
        = suc x' , suc & p'

⊢-frame : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ Θ : Mults cs}
        → (Ξ : Mults cs)
        → Θ ⊎ Δ ≡ Γ
        → γ w Γ ⊢ P ⊠ Θ
        → γ w (Ξ ⊎ Δ) ⊢ P ⊠ Ξ
⊢-frame Ξ eq end rewrite ⊎-cancelˡ-≡ (trans eq (sym (⊎-idʳ _))) | ⊎-idʳ Ξ = end
⊢-frame Ξ eq (base ⊢P) = base (⊢-frame (Ξ , _) (_,_ & eq ⊗ refl) ⊢P)
⊢-frame Ξ eq (chan t m μ ⊢P) with ⊢-frame (Ξ , ω0 ↑ ω0 ↓) (_,_ & eq ⊗ +ᵥ-idˡ _) ⊢P
⊢-frame Ξ eq (chan t m μ ⊢P) | ⊢P' rewrite +-idˡ μ = chan t m μ ⊢P'
⊢-frame Ξ eq (recv x ⊢P) with ∋-⊆ x | ⊢-⊆ ⊢P
⊢-frame Ξ eq (recv x ⊢P) | l , refl | (r , _) , refl = recv _ (⊢-frame _ refl ⊢P)
  |> subst (λ ● → _ w _ ⊢ ● ⦅⦆ _ ⊠ _) (sym (proj₂ (∋-frame (Ξ ⊎ r) refl x)))
  |> subst (λ ● → _ w ● ⊢ _ ⊠ Ξ) (begin
    ((Ξ ⊎ r) ⊎ l)
      ≡⟨ ⊎-assoc _ _ _ ⟩
    (Ξ ⊎ (r ⊎ l))
      ≡˘⟨ cong (λ ● → _ ⊎ ●) (⊎-cancelˡ-≡ (trans eq (⊎-assoc _ _ _))) ⟩
    (Ξ ⊎ _)
      ∎)
⊢-frame Ξ eq (send x y ⊢P) with ∋-⊆ x | ∋-⊆ y | ⊢-⊆ ⊢P
⊢-frame Ξ eq (send x y ⊢P) | l , refl | m , refl | r , refl = send _ _ (⊢-frame _ refl ⊢P)
  |> subst (λ ● → _ w _ ⊢ ● ⟨ _ ⟩ _ ⊠ _) (sym (proj₂ (∋-frame ((Ξ ⊎ r) ⊎ m) refl x)))
  |> subst (λ ● → _ w _ ⊢ _ ⟨ ● ⟩ _ ⊠ _) (sym (proj₂ (∋-frame ((Ξ ⊎ r)) refl y)))
  |> subst (λ ● → _ w ● ⊢ _ ⊠ Ξ) (begin
    (((Ξ ⊎ r) ⊎ m) ⊎ l)
      ≡⟨ cong (λ ● → ● ⊎ _) (⊎-assoc _ _ _) ⟩
    ((Ξ ⊎ (r ⊎ m)) ⊎ l)
      ≡⟨ ⊎-assoc _ _ _ ⟩
    (Ξ ⊎ ((r ⊎ m) ⊎ l))
      ≡˘⟨ cong (λ ● → _ ⊎ ●) (⊎-cancelˡ-≡ (trans eq (trans (cong (λ ● → ● ⊎ _) (⊎-assoc _ _ _)) (⊎-assoc _ _ _)))) ⟩
    (Ξ ⊎ _)
      ∎)
⊢-frame Ξ eq (comp ⊢P ⊢Q) with ⊢-⊆ ⊢P | ⊢-⊆ ⊢Q
⊢-frame Ξ eq (comp ⊢P ⊢Q) | l , refl | r , refl = comp (⊢-frame _ refl ⊢P) (⊢-frame _ refl ⊢Q)
  |> subst (λ ● → _ w ● ⊢ _ ⊠ Ξ) (begin
    ((Ξ ⊎ r) ⊎ l)
      ≡⟨ ⊎-assoc _ _ _ ⟩
    (Ξ ⊎ (r ⊎ l))
      ≡˘⟨ cong (λ ● → _ ⊎ ●) (⊎-cancelˡ-≡ (trans eq (⊎-assoc _ _ _))) ⟩
    (Ξ ⊎ _)
      ∎)

comp-comm : {ss : Shapes n} {cs : Cards ss} {γ : Types ss}
          → (Γ Ξ : Mults cs)
          → γ w Γ ⊢ P ∥ Q ⊠ Ξ
          → γ w Γ ⊢ Q ∥ P ⊠ Ξ
comp-comm Γ Ξ (comp ⊢P ⊢Q) with ⊢-⊆ ⊢P | ⊢-⊆ ⊢Q
comp-comm Γ Ξ (comp ⊢P ⊢Q) | l , refl | r , refl = comp
  (⊢Q |> ⊢-frame (Ξ ⊎ l) refl              ∶ _ w (Ξ ⊎ l) ⊎ r ⊢ _ ⊠ (Ξ ⊎ l)
      |> subst (λ ●                        → _ w ●           ⊢ _ ⊠ (Ξ ⊎ l))
        (trans (⊎-assoc _ _ _)
        (trans (_⊎_ & refl ⊗ ⊎-comm _ _)
               (sym (⊎-assoc _ _ _))))     ∶ _ w (Ξ ⊎ r) ⊎ l ⊢ _ ⊠ (Ξ ⊎ l))
  (⊢P |> ⊢-frame _ refl                    ∶ _ w Ξ ⊎ l       ⊢ _ ⊠ Ξ)


subject-cong : SubjectCongruence
subject-cong comp-assoc (comp ⊢P (comp ⊢Q ⊢R)) = comp (comp ⊢P ⊢Q) ⊢R
subject-cong comp-symm (comp ⊢P ⊢Q) = comp-comm _ _ (comp ⊢P ⊢Q)
subject-cong comp-end (comp ⊢P end) = ⊢P
subject-cong scope-end (chan t c μ ⊢P) = {!⊢P!}
subject-cong base-end (base end) = end
subject-cong (scope-ext u) (chan t c μ (comp ⊢P ⊢Q)) = comp {!!} {!!}
subject-cong (base-ext u) (base (comp ⊢P ⊢Q)) = comp {!!} {!!}
subject-cong scope-scope-comm (chan t c μ (chan t₁ c₁ μ₁ ⊢P)) = chan t₁ c₁ μ₁ (chan t c μ {!!})
subject-cong scope-base-comm (chan t c μ (base ⊢P)) = base (chan t c μ {!!})
subject-cong base-base-comm (base (base ⊢P)) = {!!}
subject-cong cong-refl ⊢P = ⊢P
subject-cong (cong-symm comp-assoc) (comp (comp ⊢P ⊢Q) ⊢R) = comp ⊢P (comp ⊢Q ⊢R)
subject-cong (cong-symm comp-symm) (comp ⊢P ⊢Q) = {!!}
subject-cong (cong-symm comp-end) ⊢P = comp ⊢P end
subject-cong (cong-symm scope-end) ⊢P = chan B[ 0 ] [] 0∙ {!end!}
subject-cong (cong-symm base-end) ⊢P = base {!end!}
subject-cong (cong-symm (scope-ext u)) (comp ⊢P (chan t c μ ⊢Q)) = {!!}
subject-cong (cong-symm (base-ext u)) (comp ⊢P (base ⊢Q)) = {!!}
subject-cong (cong-symm scope-scope-comm) (chan t c μ (chan t₁ c₁ μ₁ ⊢P)) = {!!}
subject-cong (cong-symm scope-base-comm) (base (chan t c μ ⊢P)) = {!!}
subject-cong (cong-symm base-base-comm) (base (base ⊢P)) = {!!}
subject-cong (cong-symm cong-refl) ⊢P = ⊢P
subject-cong (cong-symm (cong-symm P≅Q)) ⊢P = subject-cong P≅Q ⊢P
subject-cong (cong-symm (new-cong P≅Q)) (chan t c μ ⊢P) = chan t c μ (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (comp-cong P≅Q)) (comp ⊢P ⊢R) = comp (subject-cong (cong-symm P≅Q) ⊢P) ⊢R
subject-cong (cong-symm (input-cong P≅Q)) (recv x ⊢P) = recv x (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (output-cong P≅Q)) (send x y ⊢P) = send x y (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (base-cong P≅Q)) (base ⊢P) = base (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (new-cong P≅Q) (chan t c μ ⊢P) = chan t c μ (subject-cong P≅Q ⊢P)
subject-cong (comp-cong P≅Q) (comp ⊢P ⊢R) = comp (subject-cong P≅Q ⊢P) ⊢R
subject-cong (input-cong P≅Q) (recv x ⊢P) = recv x (subject-cong P≅Q ⊢P)
subject-cong (output-cong P≅Q) (send x y ⊢P) = send x y (subject-cong P≅Q ⊢P)
subject-cong (base-cong P≅Q) (base ⊢P) = base (subject-cong P≅Q ⊢P)

subject-reduction : SubjectReduction
subject-reduction comm (comp (recv x ⊢P) ⊢Q) = {!⊢Q!}
subject-reduction {c = nothing} (par P⇒P') (comp ⊢P ⊢Q) = comp (subject-reduction P⇒P' ⊢P) ⊢Q
subject-reduction {c = just i} (par P⇒P') (comp ⊢P ⊢Q) = {!!}
subject-reduction (res {c = nothing} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ μ (subject-reduction P⇒Q ⊢P)
subject-reduction (res {c = just zero} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ ω0 (subject-reduction P⇒Q ⊢P)
subject-reduction (res {c = just (suc i)} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ μ (subject-reduction P⇒Q ⊢P)
subject-reduction (base {c = nothing} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (base {c = just zero} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (base {c = just (suc x)} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (struct P≅P' P'⇒Q) ⊢P = subject-reduction P'⇒Q (subject-cong P≅P' ⊢P)
