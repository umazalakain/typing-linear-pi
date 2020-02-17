open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function.Reasoning
open import Function using (_∘_)

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

open Empty using (⊥-elim)
open Unit using (⊤; tt)
open Nat using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Framing (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    P Q : Scoped n

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
⊢-frame Ξ eq (chan t m μ ⊢P) with ⊢-frame (Ξ , 0∙ ↑ 0∙ ↓) (_,_ & eq ⊗ +ᵥ-idˡ _) ⊢P
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
