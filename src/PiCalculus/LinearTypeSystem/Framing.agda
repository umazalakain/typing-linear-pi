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
open import PiCalculus.Quantifiers

module PiCalculus.LinearTypeSystem.Framing (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    i : I
    γ : PreCtx n
    t : Type
    xs ys zs : Usage (i , t)
    Γ Θ Δ Ξ : Ctx γ
    P Q : Scoped n

∋-frame : {γ : PreCtx n} {Γ Θ Δ Ξ Ψ : Ctx γ} {t : Type} {xs : Usage (i , t)}
        → Γ ≔ Δ ⊎ Θ → Ξ ≔ Δ ⊎ Ψ
        → (x : γ w Γ ∋ t w xs ⊠ Θ)
        → Σ[ y ∈ γ w Ξ ∋ t w xs ⊠ Ψ ]
          toFin x ≡ toFin y

∋-frame {Γ = _ -, _} {_ -, ys} {_ -, _} {_ -, _} {Ψ -, _} {xs = xs} (Γ≔ , x≔) (Ξ≔ , x'≔) (zero {check = check}) with ∙ᵥ-compute xs ys
∋-frame {Γ = _ -, _} {_ -, ys} {_ -, _} {_ -, _} {Ψ -, _} {xs = xs} (Γ≔ , x≔) (Ξ≔ , x'≔) (zero {check = tt}) | yes (_ , p)
  rewrite ⊎-cancelˡ Γ≔ (⊎-idˡ _) | ⊎-unique Ξ≔ (⊎-idˡ Ψ) | ∙ᵥ-cancelˡ x≔ p | ∙ᵥ-compute-unique x'≔ = zero {check = fromWitness (_ , x'≔)} , refl
∋-frame {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} {Ψ -, _} (Γ≔ , x≔) (Ξ≔ , x'≔) (suc x) with ∋-frame Γ≔ Ξ≔ x
∋-frame {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} {Ψ -, xs} (Γ≔ , x≔) (Ξ≔ , x'≔) (suc x) | (y≔ , eq)
  rewrite ∙ᵥ-cancelˡ x≔ (∙ᵥ-idˡ _) | ∙ᵥ-unique x'≔ (∙ᵥ-idˡ xs) = suc y≔ , cong suc eq

postulate
  ⊢-frame : {γ : PreCtx n} {Γ Δ Θ Ξ Ψ : Ctx γ}
          → Γ ≔ Δ ⊎ Θ → γ w Γ ⊢ P ⊠ Θ
          → Ξ ≔ Δ ⊎ Ψ → γ w Ξ ⊢ P ⊠ Ψ

{-
⊢-frame {Ψ = Ψ} Γ≔ end Ξ≔ rewrite ⊎-cancelˡ Γ≔ (⊎-idˡ _) | ⊎-unique Ξ≔ (⊎-idˡ Ψ) = end
⊢-frame Γ≔ (base ⊢P) Ξ≔ = base (⊢-frame {Δ = _ -, []} (Γ≔ , _) ⊢P (Ξ≔ , _))
⊢-frame Γ≔ (chan t m μ ⊢P) Ξ≔ = chan t m μ (⊢-frame {Δ = _ -, μ ↑ μ ↓} (Γ≔  , (_ , ∙-idʳ _) , ∙-idʳ _ ) ⊢P (Ξ≔ , (_ , (∙-idʳ _)) , (∙-idʳ _)))
⊢-frame Γ≔ (recv x ⊢P) Ξ≔ = {!!}
⊢-frame Γ≔ (send x y ⊢P) Ξ≔ = {!!}
⊢-frame Γ≔ (comp ⊢P ⊢Q) Ξ≔ = comp (⊢-frame (proj₂ (⊢-⊎ ⊢P)) ⊢P _) (⊢-frame (proj₂ (⊢-⊎ ⊢Q)) ⊢Q _)

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
-}
