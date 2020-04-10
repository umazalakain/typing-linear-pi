open import Relation.Nullary.Decidable using (toWitness; fromWitness)
open import Relation.Nullary using (yes; no)
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
open Product using (_×_; _,_; proj₁; proj₂)

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
    i j : Fin n
    idx : Idx
    idxs : Idxs n
    γ : PreCtx n
    t : Type
    x y z : Carrier idx
    Γ Θ Δ Ξ : Ctx idxs
    P Q : Scoped n

∋-frame : {γ : PreCtx n} {idxs : Idxs n} {Γ Θ Δ Ξ Ψ : Ctx idxs} {t : Type} {x : Carrier idx ²}
        → Γ ≔ Δ ⊎ Θ → Ξ ≔ Δ ⊎ Ψ
        → γ ∝ Γ [ i ]≔ t ∝ x ⊠ Θ
        → γ ∝ Ξ [ i ]≔ t ∝ x ⊠ Ψ

∋-frame (Γ≔ , x≔) (Ξ≔ , x'≔) (zero ⦃ check ⦄)
  rewrite ⊎-uniqueˡ Γ≔ ⊎-idˡ | ⊎-unique Ξ≔ ⊎-idˡ
  | ∙²-uniqueˡ x≔ (proj₂ (toWitness check)) | ∙²-compute-unique x'≔
  = zero ⦃ fromWitness (_ , x'≔) ⦄
∋-frame (Γ≔ , x≔) (Ξ≔ , x'≔) (suc x)
  rewrite ∙²-uniqueˡ x≔ ∙²-idˡ | ∙²-unique x'≔ ∙²-idˡ
  = suc (∋-frame Γ≔ Ξ≔ x)

⊢-frame : {γ : PreCtx n} {idxs : Idxs n} {Γ Δ Θ Ξ Ψ : Ctx idxs}
        → Γ ≔ Δ ⊎ Θ → Ξ ≔ Δ ⊎ Ψ
        → γ ∝ Γ ⊢ P ⊠ Θ
        → γ ∝ Ξ ⊢ P ⊠ Ψ

⊢-frame Γ≔ Ξ≔ end rewrite ⊎-uniqueˡ Γ≔ ⊎-idˡ | ⊎-unique Ξ≔ ⊎-idˡ = end
⊢-frame Γ≔ Ξ≔ (chan t m μ ⊢P)
  = chan t m μ (⊢-frame {Δ = _ -, (μ , μ)} (Γ≔ , ∙²-idʳ) (Ξ≔ , ∙²-idʳ) ⊢P)
⊢-frame Γ≔ Ξ≔ (recv ∋i ⊢P) with ∋-⊎ ∋i | ⊢-⊎ ⊢P
⊢-frame Γ≔ Ξ≔ (recv ∋i ⊢P) | i≔ | (_ -, _) , (P≔ , x≔) =
  let iP≔           = ⊎-comp i≔ P≔ Γ≔
      _ , i'≔ , P'≔ = ⊎-assoc Ξ≔ iP≔
   in recv (∋-frame i≔ i'≔ ∋i) (⊢-frame (P≔ , x≔) (P'≔ , x≔) ⊢P)
⊢-frame Γ≔ Ξ≔ (send ∋i ∋j ⊢P) with ∋-⊎ ∋i | ∋-⊎ ∋j | ⊢-⊎ ⊢P
⊢-frame Γ≔ Ξ≔ (send ∋i ∋j ⊢P) | i≔ | j≔ | _ , P≔ =
  let [ij]P≔         = ⊎-comp (⊎-trans i≔ j≔) P≔ Γ≔
      _ , ij'≔ , P'≔ = ⊎-assoc Ξ≔ [ij]P≔
      ij≔            = ⊎-comp i≔ j≔ (⊎-trans i≔ j≔)
      _ , i'≔ , j'≔  = ⊎-assoc ij'≔ ij≔
   in send (∋-frame i≔ i'≔ ∋i) (∋-frame j≔ j'≔ ∋j) (⊢-frame P≔ P'≔ ⊢P)
⊢-frame Γ≔ Ξ≔ (comp ⊢P ⊢Q) with ⊢-⊎ ⊢P | ⊢-⊎ ⊢Q
⊢-frame Γ≔ Ξ≔ (comp ⊢P ⊢Q) | _ , P≔ | _ , Q≔ =
  let PQ≔           = ⊎-comp P≔ Q≔ Γ≔
      _ , P'≔ , Q'≔ = ⊎-assoc Ξ≔ PQ≔
   in comp (⊢-frame P≔ P'≔ ⊢P) (⊢-frame Q≔ Q'≔ ⊢Q)
