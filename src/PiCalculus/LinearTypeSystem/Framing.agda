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
          toFin y ≡ toFin x

∋-frame {Γ = _ -, _} {_ -, ys} {_ -, _} {_ -, _} {Ψ -, _} {xs = xs} (Γ≔ , x≔) (Ξ≔ , x'≔) (zero {check = check})
  rewrite ⊎-cancelˡ Γ≔ (⊎-idˡ _) | ⊎-unique Ξ≔ (⊎-idˡ Ψ)
  | ∙ᵥ-cancelˡ x≔ (proj₂ (toWitness check)) | ∙ᵥ-compute-unique x'≔
  = zero {check = fromWitness (_ , x'≔)} , refl
∋-frame {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} {Ψ -, _} (Γ≔ , x≔) (Ξ≔ , x'≔) (suc x) with ∋-frame Γ≔ Ξ≔ x
∋-frame {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} {Ψ -, xs} (Γ≔ , x≔) (Ξ≔ , x'≔) (suc x) | (y≔ , eq)
  rewrite ∙ᵥ-cancelˡ x≔ (∙ᵥ-idˡ _) | ∙ᵥ-unique x'≔ (∙ᵥ-idˡ xs) = suc y≔ , cong suc eq

⊢-frame : {γ : PreCtx n} {Γ Δ Θ Ξ Ψ : Ctx γ}
        → Γ ≔ Δ ⊎ Θ → Ξ ≔ Δ ⊎ Ψ
        → γ w Γ ⊢ P ⊠ Θ → γ w Ξ ⊢ P ⊠ Ψ

⊢-frame {Ψ = Ψ} Γ≔ Ξ≔ end rewrite ⊎-cancelˡ Γ≔ (⊎-idˡ _) | ⊎-unique Ξ≔ (⊎-idˡ Ψ) = end
⊢-frame Γ≔ Ξ≔ (base ⊢P) = base (⊢-frame {Δ = _ -, []} (Γ≔ , _) (Ξ≔ , _) ⊢P)
⊢-frame Γ≔ Ξ≔ (chan t m μ ⊢P)
  = chan t m μ (⊢-frame {Δ = _ -, μ ↑ μ ↓}
                        (Γ≔ , (_ , ∙-idʳ _) , ∙-idʳ _ )
                        (Ξ≔ , (_ , ∙-idʳ _) , ∙-idʳ _) ⊢P)
⊢-frame Γ≔ Ξ≔ (recv x ⊢P) with ∋-⊎ x | ⊢-⊎ ⊢P
⊢-frame Γ≔ Ξ≔ (recv x ⊢P) | _ , x≔ | (_ -, _) , (P≔ , xs≔) =
  let xP≔           = ⊎-comp x≔ P≔ Γ≔
      _ , x'≔ , P'≔ = ⊎-assoc Ξ≔ xP≔
   in recv _ (⊢-frame {Δ = _ -, _} (P≔ , xs≔) (P'≔ , xs≔) ⊢P)
      |> subst (λ ● → _ w _ ⊢ ● ⦅⦆ _ ⊠ _) (proj₂ (∋-frame x≔ x'≔ x))
⊢-frame Γ≔ Ξ≔ (send x y ⊢P) with ∋-⊎ x | ∋-⊎ y | ⊢-⊎ ⊢P
⊢-frame Γ≔ Ξ≔ (send x y ⊢P) | _ , x≔ | _ , y≔ | _ , P≔ =
  let [xy]P≔         = ⊎-comp (⊎-trans x≔ y≔) P≔ Γ≔
      _ , xy'≔ , P'≔ = ⊎-assoc Ξ≔ [xy]P≔
      xy≔            = ⊎-comp x≔ y≔ (⊎-trans x≔ y≔)
      _ , x'≔ , y'≔  = ⊎-assoc xy'≔ xy≔
   in send _ _ (⊢-frame P≔ P'≔ ⊢P)
      |> subst (λ ● → _ w _ ⊢ ● ⟨ _ ⟩ _ ⊠ _) (proj₂ (∋-frame x≔ x'≔ x))
      |> subst (λ ● → _ w _ ⊢ _ ⟨ ● ⟩ _ ⊠ _) (proj₂ (∋-frame y≔ y'≔ y))
⊢-frame Γ≔ Ξ≔ (comp ⊢P ⊢Q) with ⊢-⊎ ⊢P | ⊢-⊎ ⊢Q
⊢-frame Γ≔ Ξ≔ (comp ⊢P ⊢Q) | _ , P≔ | _ , Q≔ =
  let PQ≔           = ⊎-comp P≔ Q≔ Γ≔
      _ , P'≔ , Q'≔ = ⊎-assoc Ξ≔ PQ≔
   in comp (⊢-frame P≔ P'≔ ⊢P) (⊢-frame Q≔ Q'≔ ⊢Q)
