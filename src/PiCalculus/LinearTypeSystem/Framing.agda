{-# OPTIONS --safe #-} -- --without-K #-}

open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_)

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
import Data.Vec.Relation.Unary.All.Properties as Allₚ


import PiCalculus.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Algebras

module PiCalculus.LinearTypeSystem.Framing (Ω : Algebras) where
open Algebras Ω
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
    x y z : Usage idx
    Γ Θ Δ Ξ : Ctx idxs
    P Q : Scoped n

⊢-frame : {γ : PreCtx n} {idxs : Idxs n} {Γ Δ Θ Ξ Ψ : Ctx idxs}
        → Γ ≔ Δ ⊗ Θ → Ξ ≔ Δ ⊗ Ψ
        → γ ； Γ ⊢ P ▹ Θ
        → γ ； Ξ ⊢ P ▹ Ψ

⊢-frame Γ≔ Ξ≔ 𝟘 rewrite ⊗-uniqueˡ Γ≔ ⊗-idˡ | ⊗-unique Ξ≔ ⊗-idˡ = 𝟘
⊢-frame Γ≔ Ξ≔ (ν ts μ ⊢P)
  = ν ts μ (⊢-frame {Δ = _ -, (μ , μ)} (Γ≔ , ∙²-idʳ) (Ξ≔ , ∙²-idʳ) ⊢P)
⊢-frame Γ≔ Ξ≔ ((t , ∋i) ⦅⦆ ⊢P) with ∋-⊗ ∋i | ⊢-⊗ ⊢P
⊢-frame {idxs = idxs} Γ≔ Ξ≔ ((t , ∋i) ⦅⦆ ⊢P) | _ , i≔ , _ | Δ , P≔ rewrite sym (Allₚ.++⁺∘++⁻ idxs Δ) =
  let Pₗ≔ , Pᵣ≔     = ⊗-++⁻ (proj₁ (Allₚ.++⁻ idxs Δ)) P≔
      iP≔           = ⊗-comp i≔ Pₗ≔ Γ≔
      _ , i'≔ , P'≔ = ⊗-assoc Ξ≔ iP≔
  in (t , ∋-frame i≔ i'≔ ∋i) ⦅⦆ ⊢-frame P≔ (⊗-++⁺ P'≔ Pᵣ≔) ⊢P
⊢-frame Γ≔ Ξ≔ ((ti , ∋i) ⟨ tj , ∋js ⟩ ⊢P) with ∋-⊗ ∋i | ⊇-⊗ ∋js | ⊢-⊗ ⊢P
⊢-frame Γ≔ Ξ≔ ((ti , ∋i) ⟨ tj , ∋js ⟩ ⊢P) | _ , i≔ , _ | _ , js≔ , _ | _ , P≔ =
  let _ , ijs≔ , _    = ⊗-assoc⁻¹ i≔ js≔
      [ijs]P≔         = ⊗-comp ijs≔ P≔ Γ≔
      _ , ijs'≔ , P'≔ = ⊗-assoc Ξ≔ [ijs]P≔
      ijs≔            = ⊗-comp i≔ js≔ ijs≔
      _ , i'≔ , js'≔  = ⊗-assoc ijs'≔ ijs≔
   in (ti , ∋-frame i≔ i'≔ ∋i) ⟨ tj , ⊇-frame js≔ js'≔ ∋js ⟩ ⊢-frame P≔ P'≔ ⊢P
⊢-frame Γ≔ Ξ≔ (⊢P ∥ ⊢Q) with ⊢-⊗ ⊢P | ⊢-⊗ ⊢Q
⊢-frame Γ≔ Ξ≔ (⊢P ∥ ⊢Q) | _ , P≔ | _ , Q≔ =
  let PQ≔           = ⊗-comp P≔ Q≔ Γ≔
      _ , P'≔ , Q'≔ = ⊗-assoc Ξ≔ PQ≔
   in ⊢-frame P≔ P'≔ ⊢P ∥ ⊢-frame Q≔ Q'≔ ⊢Q
