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

module PiCalculus.LinearTypeSystem.Framing (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    i : I
    is : Vec I n
    γ : PreCtx n
    t : Type
    xs ys zs : Cs i
    Γ Θ Δ Ξ : Ctx is
    P Q : Scoped n

∋-frame : {γ : PreCtx n} {idxs : Vec I n} {Γ Θ Δ Ξ Ψ : Ctx idxs} {t : Type} {xs : Cs i}
        → Γ ≔ Δ ⊎ Θ → Ξ ≔ Δ ⊎ Ψ
        → (x : γ ∝ Γ ∋ t ∝ xs ⊠ Θ)
        → Σ[ y ∈ γ ∝ Ξ ∋ t ∝ xs ⊠ Ψ ]
          toFin y ≡ toFin x

∋-frame {Γ = _ -, _} {_ -, ys} {_ -, _} {_ -, _} {Ψ -, _} {xs = xs} (Γ≔ , x≔) (Ξ≔ , x'≔) (zero {check = check})
  rewrite ⊎-uniqueˡ Γ≔ (⊎-idˡ _) | ⊎-unique Ξ≔ (⊎-idˡ Ψ)
  | ∙-uniqueˡ x≔ (proj₂ (toWitness check)) | ∙-compute-unique x'≔
  = zero {check = fromWitness (_ , x'≔)} , refl
∋-frame {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} {Ψ -, _} (Γ≔ , x≔) (Ξ≔ , x'≔) (suc x) with ∋-frame Γ≔ Ξ≔ x
∋-frame {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} {Ψ -, xs} (Γ≔ , x≔) (Ξ≔ , x'≔) (suc x) | (y≔ , eq)
  rewrite ∙-uniqueˡ x≔ (∙-idˡ _) | ∙-unique x'≔ (∙-idˡ xs) = suc y≔ , cong suc eq

⊢-frame : {γ : PreCtx n} {idxs : Vec I n} {Γ Δ Θ Ξ Ψ : Ctx idxs}
        → Γ ≔ Δ ⊎ Θ → Ξ ≔ Δ ⊎ Ψ
        → γ ∝ Γ ⊢ P ⊠ Θ → γ ∝ Ξ ⊢ P ⊠ Ψ

⊢-frame {Ψ = Ψ} Γ≔ Ξ≔ end rewrite ⊎-uniqueˡ Γ≔ (⊎-idˡ _) | ⊎-unique Ξ≔ (⊎-idˡ Ψ) = end
⊢-frame Γ≔ Ξ≔ (chan t m μ ⊢P)
  = chan t m μ (⊢-frame {Δ = _ -, μ} (Γ≔ , ∙-idʳ _) (Ξ≔ , ∙-idʳ _) ⊢P)
⊢-frame Γ≔ Ξ≔ (recv x ⊢P) with ⊢-⊎ ⊢P
⊢-frame Γ≔ Ξ≔ (recv x ⊢P) | (_ -, _) , (P≔ , xs≔) =
  let xP≔           = ⊎-comp (∋-⊎ x) P≔ Γ≔
      _ , x'≔ , P'≔ = ⊎-assoc Ξ≔ xP≔
   in recv _ (⊢-frame {Δ = _ -, _} (P≔ , xs≔) (P'≔ , xs≔) ⊢P)
      |> subst (λ ● → _ ∝ _ ⊢ ● ⦅⦆ _ ⊠ _) (proj₂ (∋-frame (∋-⊎ x) x'≔ x))
⊢-frame Γ≔ Ξ≔ (send x y ⊢P) with ∋-⊎ x | ∋-⊎ y | ⊢-⊎ ⊢P
⊢-frame Γ≔ Ξ≔ (send x y ⊢P) | x≔ | y≔ | _ , P≔ =
  let [xy]P≔         = ⊎-comp (⊎-trans x≔ y≔) P≔ Γ≔
      _ , xy'≔ , P'≔ = ⊎-assoc Ξ≔ [xy]P≔
      xy≔            = ⊎-comp x≔ y≔ (⊎-trans x≔ y≔)
      _ , x'≔ , y'≔  = ⊎-assoc xy'≔ xy≔
   in send _ _ (⊢-frame P≔ P'≔ ⊢P)
      |> subst (λ ● → _ ∝ _ ⊢ ● ⟨ toFin (proj₁ (∋-frame y≔ y'≔ y)) ⟩ _ ⊠ _)
               (proj₂ (∋-frame x≔ x'≔ x))
      |> subst (λ ● → _ ∝ _ ⊢ _ ⟨ ● ⟩ _ ⊠ _)
               (proj₂ (∋-frame y≔ y'≔ y))
⊢-frame Γ≔ Ξ≔ (comp ⊢P ⊢Q) with ⊢-⊎ ⊢P | ⊢-⊎ ⊢Q
⊢-frame Γ≔ Ξ≔ (comp ⊢P ⊢Q) | _ , P≔ | _ , Q≔ =
  let PQ≔           = ⊎-comp P≔ Q≔ Γ≔
      _ , P'≔ , Q'≔ = ⊎-assoc Ξ≔ PQ≔
   in comp (⊢-frame P≔ P'≔ ⊢P) (⊢-frame Q≔ Q'≔ ⊢Q)
