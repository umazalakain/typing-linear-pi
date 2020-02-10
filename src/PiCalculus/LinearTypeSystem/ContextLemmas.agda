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

open import PiCalculus.Function
open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.OmegaNat

module PiCalculus.LinearTypeSystem.ContextLemmas where

private
  variable
    n : ℕ
    ss : Shapes n
    cs : Cards ss

-- Addition of contexts

_⊎_ : {ss : Shapes n} {cs : Cards ss} → Mults cs → Mults cs → Mults cs
_⊎_ {ss = []} tt tt = tt
_⊎_ {ss = _ -, _} (Γ , m) (Δ , n) = Γ ⊎ Δ , m +ᵥ n

⊎-idˡ : {ss : Shapes n} {cs : Cards ss} (Γ : Mults cs) → ε ⊎ Γ ≡ Γ
⊎-idˡ {ss = []} tt = refl
⊎-idˡ {ss = _ -, _} (Γ , m) rewrite ⊎-idˡ Γ | +ᵥ-idˡ m = refl

⊎-comm : {ss : Shapes n} {cs : Cards ss} (Γ Δ : Mults cs) → Γ ⊎ Δ ≡ Δ ⊎ Γ
⊎-comm {ss = []} tt tt = refl
⊎-comm {ss = _ -, _} (Γ , m) (Δ , n) rewrite ⊎-comm Γ Δ | +ᵥ-comm m n = refl

⊎-assoc : {ss : Shapes n} {cs : Cards ss} (Γ Δ Ξ : Mults cs) → (Γ ⊎ Δ) ⊎ Ξ ≡ Γ ⊎ (Δ ⊎ Ξ)
⊎-assoc {ss = []} tt tt tt = refl
⊎-assoc {ss = _ -, _} (Γ , m) (Δ , n) (Ξ , l) rewrite ⊎-assoc Γ Δ Ξ | +ᵥ-assoc m n l = refl

{-
0Δ : {ss : SCtx n} → CCtx ss
0Δ {ss = []} = []
0Δ {ss = _ -, _} = 0Δ -, Vec.replicate 0∙

⊎-idˡ : (Γ : CCtx ss) → 0Δ ⊎ Γ ≡ Γ
⊎-idˡ [] = refl
⊎-idˡ (Γ -, ns) rewrite ⊎-idˡ Γ | +ᵥ-idˡ ns = refl
-}


-- Capable of of contexts

_⊆_ : {ss : Shapes n} {cs : Cards ss} → Mults cs → Mults cs → Set
ϕ ⊆ Γ = Σ[ Δ ∈ _ ] Δ ⊎ ϕ ≡ Γ

⊆-refl : {ss : Shapes n} {cs : Cards ss} {Γ : Mults cs} → Γ ⊆ Γ
⊆-refl = ε , ⊎-idˡ _

⊆-trans : {ss : Shapes n} {cs : Cards ss} {Γ Ξ Θ : Mults cs} → Γ ⊆ Ξ → Ξ ⊆ Θ → Γ ⊆ Θ
⊆-trans (Δ₁ , refl) (Δ₂ , refl) = Δ₂ ⊎ Δ₁ , ⊎-assoc _ _ _

⊆-cong : {ss : Shapes n} {cs : Cards ss} {Γ Δ : Mults cs}
       → {s : Shape} {c : Card s} {m l : Mult s c}
       → Δ ⊆ Γ → l ≤ᵥ m → _⊆_ {ss = ss -, s} (Δ , l) (Γ , m)
⊆-cong (ctx , refl) (card , refl) = (ctx , card) , _,_ & refl ⊗ refl

{-
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
-}
