open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (fromWitness; toWitness)
open import Function using (_∘_)
open import Function.Reasoning

import Data.Empty as Empty
import Data.Product as Product
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
    s : Shape
    t : Type s
    c : Capability s
    n : ℕ
    ss : SCtx n
    γ : TCtx ss
    Γ Δ ϕ Κ : CCtx ss
    P Q : Scoped n

∋-⊆ : {s : Shape} {t : Type s} {c : Capability s}
    → γ w Γ ∋ t w c ⊠ ϕ → ϕ ⊆ Γ
∋-⊆ zero = _ , (_-,_ & ⊎-idˡ _ ⊗ +ᵥ-comm _ _)
∋-⊆ (suc x) with ∋-⊆ x
∋-⊆ (suc x) | _ , eq = _ , (_-,_ & eq ⊗ +ᵥ-idˡ _)

⊢-⊆ : γ w Γ ⊢ P ⊠ ϕ → ϕ ⊆ Γ
⊢-⊆ end = ⊆-refl
⊢-⊆ (base ⊢P) = ⊆-tail (⊢-⊆ ⊢P)
⊢-⊆ (chan t c μ ⊢P) = ⊆-tail (⊢-⊆ ⊢P)
⊢-⊆ (recv x ⊢P) = ⊆-trans (⊆-tail (⊢-⊆ ⊢P)) (∋-⊆ x)
⊢-⊆ (send x y ⊢P) = ⊆-trans (⊢-⊆ ⊢P) (⊆-trans (∋-⊆ y) (∋-⊆ x))
⊢-⊆ (comp ⊢P ⊢Q) = ⊆-trans (⊢-⊆ ⊢Q) (⊢-⊆ ⊢P)

∋-<ω> : {s : Shape} {t : Type s} {c : Capability s}
      → γ w Γ ∋ t w c ⊠ Δ → Δ <ω> Γ
∋-<ω> (zero ⦃ p ⦄) = <ω>-refl , ωᵥ-sym (toWitness p)
∋-<ω> (suc Γ∋c) = (∋-<ω> Γ∋c) , ωᵥ-refl

⊢-<ω> : γ w Γ ⊢ P ⊠ Δ → Δ <ω> Γ
⊢-<ω> end = <ω>-refl
⊢-<ω> (base ⊢P) with ⊢-<ω> ⊢P
⊢-<ω> (base ⊢P) | Γ<ω>Δ , _ = Γ<ω>Δ
⊢-<ω> (chan t c μ ⊢P) with ⊢-<ω> ⊢P
⊢-<ω> (chan t c μ ⊢P) | Γ<ω>Δ , _ = Γ<ω>Δ
⊢-<ω> (recv x ⊢P) with ⊢-<ω> ⊢P
⊢-<ω> (recv x ⊢P) | Δωϕ , _ = <ω>-trans Δωϕ (∋-<ω> x)
⊢-<ω> (send x y ⊢P) = <ω>-trans (⊢-<ω> ⊢P) (<ω>-trans (∋-<ω> y) (∋-<ω> x))
⊢-<ω> (comp ⊢P ⊢Q) = <ω>-trans (⊢-<ω> ⊢Q) (⊢-<ω> ⊢P)

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


weaken : ∀ {n} {P : Scoped n} {ss : SCtx n} {γ : TCtx ss}
       → {Γ Δ : CCtx ss} (ϕ : CCtx ss)
       → γ w Γ       ⊢ P ⊠ Δ
       → γ w (ϕ ⊎ Γ) ⊢ P ⊠ (ϕ ⊎ Δ)
weaken ϕ end = end
weaken ϕ (base ⊢P) = base (weaken (ϕ -, []) ⊢P)
weaken ϕ (chan t c μ ⊢P) = chan t c μ (weaken (ϕ -, Vec.replicate 0∙) ⊢P
  |> subst (λ ● → _ w _ -, ● ↑ ● ↓ ⊢ _ ⊠ _ -, ((0∙ + (μ ∸ μ)) ↑ 0∙ + (μ ∸ μ) ↓)) (+-idˡ μ)
  |> subst (λ ● → _ w _ -, μ ↑ μ ↓ ⊢ _ ⊠ _ -, (●              ↑ ●            ↓)) (+-idˡ (μ ∸ μ))
  )
weaken ϕ (recv {c = c} x ⊢P) rewrite (proj₂ (⊎-toFin ϕ x)) = recv _ (weaken (ϕ -, Vec.replicate 0∙) ⊢P
  |> subst (λ ● → _ w _ -, ● ⊢ _ ⊠ _ -, (0s +ᵥ (c ∸ᵥ c))) (+ᵥ-idˡ c)
  |> subst (λ ● → _ w _ -, c ⊢ _ ⊠ _ -, ●) (+ᵥ-idˡ (c ∸ᵥ c))
  )
weaken ϕ (send x y ⊢P) rewrite (proj₂ (⊎-toFin ϕ x)) | (proj₂ (⊎-toFin ϕ y )) = send _ _ (weaken ϕ ⊢P)
weaken ϕ (comp ⊢P ⊢Q) = comp (weaken ϕ ⊢P) (weaken ϕ ⊢Q)

postulate

  strengthen : ∀ {n} {P : Scoped n} {ss : SCtx n} {γ : TCtx ss} {Γ Δ : CCtx ss}
             → γ w Γ       ⊢ P ⊠ Δ
             → γ w (Γ / Δ) ⊢ P ⊠ (Δ / Δ)

comp-comm : ∀ {n} {P Q : Scoped n} {ss : SCtx n} {γ : TCtx ss}
          → (Γ ϕ : CCtx ss)
          → γ w Γ ⊢ P ∥ Q ⊠ ϕ
          → γ w Γ ⊢ Q ∥ P ⊠ ϕ

comp-comm Γ ϕ (comp {Δ = Δ} ⊢P ⊢Q) = {!!}
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

subject-cong : SubjectCongruence
subject-cong comp-assoc (comp ⊢P (comp ⊢Q ⊢R)) = comp (comp ⊢P ⊢Q) ⊢R
subject-cong comp-symm (comp ⊢P ⊢Q) = {!!}
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
subject-reduction (res {c = just zero} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ (consume μ) (subject-reduction P⇒Q ⊢P)
subject-reduction (res {c = just (suc i)} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ μ (subject-reduction P⇒Q ⊢P)
subject-reduction (base {c = nothing} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (base {c = just zero} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (base {c = just (suc x)} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (struct P≅P' P'⇒Q) ⊢P = subject-reduction P'⇒Q (subject-cong P≅P' ⊢P)
