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
∋-⊆ (zero {Γ = Γ}) = (ε , _) , _,_ & ⊎-idʳ _ ⊗ +ᵥ-comm _ _
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

{-
⊎-toFin : {ss : SCtx n} {γ : TCtx ss} {Γ Δ : CCtx ss}
        → {s : Shape} {t : Type s} {c : Capability s}
        → (ϕ : CCtx ss) (x : γ w Γ ∋ t w c ⊠ Δ)
        → Σ[ y ∈ γ w ϕ ⊎ Γ ∋ t w c ⊠ ϕ ⊎ Δ ]
          toFin x ≡ toFin y
⊎-toFin (ϕ -, ls) (zero {ms = ms} {ns = ns} ⦃ p ⦄)
  rewrite sym (+ᵥ-+ᵥ-assoc ls ms ns)
  = zero ⦃ fromWitness {!ωᵥ-cong ?!} ⦄ , refl
⊎-toFin (ϕ -, ls) (suc x) with ⊎-toFin ϕ x
⊎-toFin (ϕ -, ls) (suc x) | x' , eq = suc x' , suc & eq
             -}

frame : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ Ξ Θ : Mults cs}
      → Γ ≡ Θ ⊎ Δ
      → γ w Γ ⊢ P ⊠ Θ
      → γ w (Ξ ⊎ Δ) ⊢ P ⊠ Θ
frame eq end = {!!}
frame eq (base ⊢P) = base (frame (_,_ & eq ⊗ refl) ⊢P)
frame {Ξ = Ξ} eq (chan t m μ ⊢P) with frame {Ξ = Ξ , ω0 ↑ ω0 ↓} (_,_ & eq ⊗ sym (+ᵥ-idˡ _)) ⊢P
frame {Ξ = Ξ} eq (chan t m μ ⊢P) | ⊢P' rewrite +-idˡ μ = chan t m μ ⊢P'
frame eq (recv x ⊢P) with frame (_,_ & {!!} ⊗ {!!}) ⊢P
frame eq (recv x ⊢P) | ⊢P' = {!recv x ?!}
frame eq (send x y ⊢P) = {!!}
frame eq (comp ⊢P ⊢Q) = comp {!!} {!!}

comp-comm : {ss : Shapes n} {cs : Cards ss} {γ : Types ss}
          → (Γ Ξ : Mults cs)
          → γ w Γ ⊢ P ∥ Q ⊠ Ξ
          → γ w Γ ⊢ Q ∥ P ⊠ Ξ

{-
  (⊢Q |> weaken Γ                        ∶ _ w  Γ ⊎ Δ      ⊢ _ ⊗  Γ ⊎ ϕ
      |> strengthen (⊆-⊎ʳ ϕ (⊢-to-⊆ ⊢P)) ∶ _ w (Γ ⊎ Δ) / Δ ⊢ _ ⊗ (Γ ⊎ ϕ) / Δ
      |> subst (λ ●                      → _ w ●           ⊢ _ ⊗ (Γ ⊎ ϕ) / Δ)
      (trans
        (⊎-/-assoc Γ ⊆-refl )
        (⊎-idʳ (<ω>-sym (⊢-to-<ω> ⊢P)))
      )                                  ∶ _ w Γ           ⊢ _ ⊗ (Γ ⊎ ϕ) / Δ
      |> subst (λ ●                      → _ w _           ⊢ _ ⊗ ●)
      (trans
        (cong (_/ Δ) (⊎-comm Γ ϕ))
        (⊎-/-assoc ϕ (⊢-to-⊆ ⊢P))
      )                                  ∶ _ w Γ           ⊢ _ ⊗ ϕ ⊎ (Γ / Δ)
      )
  (⊢P |> strengthen ⊆-refl               ∶ _ w      Γ / Δ  ⊢ _ ⊗      (Δ / Δ)
      |> weaken ϕ                        ∶ _ w ϕ ⊎ (Γ / Δ) ⊢ _ ⊗ (ϕ ⊎ (Δ / Δ))
      |> subst (λ ●                      → _ w ϕ ⊎ (Γ / Δ) ⊢ _ ⊗ ●)
      (⊎-idʳ (⊢-to-<ω> ⊢Q))              ∶ _ w ϕ ⊎ (Γ / Δ) ⊢ _ ⊗ ϕ
      )
      -}

{-
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
-}
