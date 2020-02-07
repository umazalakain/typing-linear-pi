open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂; proj₁)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl; subst; trans; cong)
open import Function using (_∘_)

import Level as L
import Data.Fin.Properties as Finₚ
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Vec.Relation.Unary.All as All
import Data.Vec.Relation.Unary.All.Properties as Allₚ
import Data.Fin as Fin
import Data.Bool as Bool

open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Bool using (T)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.OmegaNat

module PiCalculus.LinearTypeSystem.ContextLemmas where

private
  variable
    n : ℕ
    ss : SCtx n
    Γ Δ ϕ : CCtx ss

-- Addition of contexts

_⊎_ : (Γ Δ : CCtx ss) → CCtx ss
[] ⊎ [] = []
(Γ -, ms) ⊎ (Δ -, ns) = (Γ ⊎ Δ) -, (ms +ᵥ ns)

⊎-comm : (Γ Δ : CCtx ss) → Γ ⊎ Δ ≡ Δ ⊎ Γ
⊎-comm [] [] = refl
⊎-comm (Γ -, ms) (Δ -, ns) rewrite ⊎-comm Γ Δ | +ᵥ-comm ms ns = refl

⊎-assoc : (Γ Δ ϕ : CCtx ss) → (Γ ⊎ Δ) ⊎ ϕ ≡ Γ ⊎ (Δ ⊎ ϕ)
⊎-assoc [] [] [] = refl
⊎-assoc (Γ -, ms) (Δ -, ns) (ϕ -, ls) rewrite ⊎-assoc Γ Δ ϕ | +ᵥ-+ᵥ-assoc ms ns ls = refl

0Δ : {ss : SCtx n} → CCtx ss
0Δ {ss = []} = []
0Δ {ss = _ -, _} = 0Δ -, Vec.replicate 0∙

⊎-idˡ : (Γ : CCtx ss) → 0Δ ⊎ Γ ≡ Γ
⊎-idˡ [] = refl
⊎-idˡ (Γ -, ns) rewrite ⊎-idˡ Γ | +ᵥ-idˡ ns = refl

-- Preservation of infinity for contexts

_<ω>_ : (Γ Δ : CCtx ss) → Set
[] <ω> [] = ⊤
(Γ -, ms) <ω> (Δ -, ns) = (Γ <ω> Δ) × (ms ~ω~ᵥ ns)

<ω>-refl : {Γ : CCtx ss} → Γ <ω> Γ
<ω>-refl {Γ = []} = tt
<ω>-refl {Γ = Γ -, ms} = <ω>-refl , ωᵥ-refl

<ω>-sym : {Γ Δ : CCtx ss} → Γ <ω> Δ → Δ <ω> Γ
<ω>-sym {Γ = []} {[]} tt = tt
<ω>-sym {Γ = _ -, _} {_ -, _} (Γ<ω>Δ , ms~ω~ᵥns) = <ω>-sym Γ<ω>Δ , ωᵥ-sym ms~ω~ᵥns

<ω>-trans : {Γ Δ ϕ : CCtx ss} → Γ <ω> Δ → Δ <ω> ϕ → Γ <ω> ϕ
<ω>-trans {Γ = []} {[]} {[]} tt tt = tt
<ω>-trans {Γ = _ -, _} {_ -, _} {_ -, _} (ΓωΔ , msωns) (Δωϕ , nsωls)
  = (<ω>-trans ΓωΔ Δωϕ) , ωᵥ-trans msωns nsωls

-- Capable of of contexts

_⊆_ : CCtx ss → CCtx ss → Set
ϕ ⊆ Γ = Σ[ Δ ∈ _ ] Δ ⊎ ϕ ≡ Γ

⊆-refl : {Γ : CCtx ss} → Γ ⊆ Γ
⊆-refl = 0Δ , ⊎-idˡ _

⊆-trans : {Γ Ξ ϕ : CCtx ss} → Γ ⊆ Ξ → Ξ ⊆ ϕ → Γ ⊆ ϕ
⊆-trans (Δ₁ , refl) (Δ₂ , refl) = Δ₂ ⊎ Δ₁ , ⊎-assoc _ _ _

⊆-⊎ˡ : {Γ Ξ : CCtx ss} (ϕ : CCtx ss) → Γ ⊆ Ξ → Γ ⊆ (ϕ ⊎ Ξ)
⊆-⊎ˡ ϕ (Δ , refl) = ϕ ⊎ Δ , ⊎-assoc _ _ _

⊆-⊎ʳ : {Γ Ξ : CCtx ss} (ϕ : CCtx ss) → Γ ⊆ Ξ → Γ ⊆ (Ξ ⊎ ϕ)
⊆-⊎ʳ ϕ (Δ , refl) = ϕ ⊎ Δ , trans (⊎-assoc _ _ _) (⊎-comm _ _)

⊆-tail : ∀ {Γ Ξ : CCtx ss} {s : Shape} {ms ns : Capability s} → _⊆_ {ss = s ∷ ss} (Γ -, ms) (Ξ -, ns) → Γ ⊆ Ξ
⊆-tail (_ -, _ , eq) = _ , cong All.tail eq

-- Substraction of contexts

_/_ : CCtx ss → CCtx ss → CCtx ss
[] / [] = []
(Γ -, ms) / (Δ -, ns) = (Γ / Δ) -, (ms ∸ᵥ ns)

{-
⊎-/-assoc : (Γ : CCtx ss) {Δ ϕ : CCtx ss}
          → (ϕ⊆Δ : ϕ ⊆ Δ) → (Γ ⊎ Δ) / ϕ ≡ Γ ⊎ (Δ / ϕ)
⊎-/-assoc [] {[]} {[]} tt = refl
⊎-/-assoc (Γ -, ms) {Δ -, _} {ϕ -, _} (ns≥ᵥls , ϕ⊆Δ)
  rewrite ⊎-/-assoc Γ ϕ⊆Δ
        | +ᵥ-∸ᵥ-assoc ms ns≥ᵥls = refl
        -}
