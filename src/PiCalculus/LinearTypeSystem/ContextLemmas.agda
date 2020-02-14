open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl; subst; trans; cong)
open import Function using (_∘_)

import Level as L
import Data.Product as Product
import Data.Fin.Properties as Finₚ
import Data.Product.Properties as Productₚ
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Vec.Relation.Unary.All as All
import Data.Vec.Relation.Unary.All.Properties as Allₚ
import Data.Fin as Fin
import Data.Bool as Bool

open Product using (Σ; Σ-syntax; _×_; _,_; proj₂; proj₁)
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

⊎-idʳ : {ss : Shapes n} {cs : Cards ss} (Γ : Mults cs) → Γ ⊎ ε ≡ Γ
⊎-idʳ {ss = []} tt = refl
⊎-idʳ {ss = _ -, _} (Γ , m) rewrite ⊎-idʳ Γ | +ᵥ-idʳ m = refl

⊎-comm : {ss : Shapes n} {cs : Cards ss} (Γ Δ : Mults cs) → Γ ⊎ Δ ≡ Δ ⊎ Γ
⊎-comm {ss = []} tt tt = refl
⊎-comm {ss = _ -, _} (Γ , m) (Δ , n) rewrite ⊎-comm Γ Δ | +ᵥ-comm m n = refl

⊎-assoc : {ss : Shapes n} {cs : Cards ss} (Γ Δ Ξ : Mults cs) → (Γ ⊎ Δ) ⊎ Ξ ≡ Γ ⊎ (Δ ⊎ Ξ)
⊎-assoc {ss = []} tt tt tt = refl
⊎-assoc {ss = _ -, _} (Γ , m) (Δ , n) (Ξ , l) rewrite ⊎-assoc Γ Δ Ξ | +ᵥ-assoc m n l = refl

⊎-cancelˡ-≡ : {ss : Shapes n} {cs : Cards ss} {Γ Δ Ξ : Mults cs} → Γ ⊎ Δ ≡ Γ ⊎ Ξ → Δ ≡ Ξ
⊎-cancelˡ-≡ {ss = []} {tt} {tt} {tt} _ = refl
⊎-cancelˡ-≡ {ss = _ -, _} {_ , _} {_ , _} {_ , _} eq
  rewrite +ᵥ-cancelˡ-≡ (Productₚ.,-injectiveʳ eq)
  | ⊎-cancelˡ-≡ (Productₚ.,-injectiveˡ eq)
  = refl

_⊆_ : {ss : Shapes n} {cs : Cards ss} → Mults cs → Mults cs → Set
ϕ ⊆ Γ = Σ[ Δ ∈ _ ] ϕ ⊎ Δ ≡ Γ

_⊆?_ : {ss : Shapes n} {cs : Cards ss} (Δ Γ : Mults cs) → Dec (Δ ⊆ Γ)
_⊆?_ {ss = []} tt tt = yes (tt , refl)
_⊆?_ {ss = _ -, _} (xs , x) (ys , y) with xs ⊆? ys | x ≤ᵥ? y
_⊆?_ {_} {_ -, _} (xs , x) (ys , y) | yes (_ , p) | yes (_ , q) = yes (_ , _,_ & p ⊗ q)
_⊆?_ {_} {_ -, _} (xs , x) (ys , y) | yes p | no ¬q = no λ {(_ , refl) → ¬q (_ , refl)}
_⊆?_ {_} {_ -, _} (xs , x) (ys , y) | no ¬p | _     = no λ {(_ , refl) → ¬p (_ , refl)}

⊆-refl : {ss : Shapes n} {cs : Cards ss} {Γ : Mults cs} → Γ ⊆ Γ
⊆-refl = ε , ⊎-idʳ _

⊆-trans : {ss : Shapes n} {cs : Cards ss} {Γ Ξ Θ : Mults cs} → Γ ⊆ Ξ → Ξ ⊆ Θ → Γ ⊆ Θ
⊆-trans (Δ₁ , refl) (Δ₂ , refl) = _ , sym (⊎-assoc _ _ _)

⊆-tail : {ss : Shapes n} {cs : Cards ss} {Γ Δ : Mults cs}
       → {s : Shape} {c : Card s} {m l : Mult s c}
       → _⊆_ {ss = _ -, s} (Δ , m) (Γ , l) → Δ ⊆ Γ
⊆-tail = Product.map proj₁ Productₚ.,-injectiveˡ

⊆-⊎ˡ : {ss : Shapes n} {cs : Cards ss} {Γ Ξ : Mults cs} (Δ : Mults cs) → Γ ⊆ Ξ → Γ ⊆ (Δ ⊎ Ξ)
⊆-⊎ˡ Δ (diff , refl) = Δ ⊎ diff , trans (⊎-comm _ _) (trans (⊎-assoc _ _ _) (cong (_ ⊎_) (⊎-comm _ _)))

_/_ : {ss : Shapes n} {cs : Cards ss} → Mults cs → Mults cs → Mults cs
Γ / Δ with Δ ⊆? Γ
(Γ / Δ) | yes (d , _) = d
(Γ / Δ) | no _ = ε

{-

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
