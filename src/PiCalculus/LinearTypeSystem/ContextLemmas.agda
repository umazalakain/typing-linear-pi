open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl; subst; trans; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitness)
open import Function using (_∘_)

import Data.Maybe as Maybe
import Data.Empty as Empty
import Data.Unit as Unit
import Data.Nat as ℕ
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
import Data.Fin as Fin

open Maybe using (nothing; just)
open Empty using (⊥)
open Unit using (⊤; tt)
open ℕ using (ℕ; zero; suc)
open Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₂; proj₁)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.ContextLemmas (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω

private
  variable
    n : ℕ
    idxs : Idxs n
    γ : PreCtx n
    idx idx' : Idx
    t : Type
    P Q : Scoped n
    i j : Fin n

only : {idxs : Idxs n} (i : Fin n) → Carrier (Vec.lookup idxs i) ² → Ctx idxs
only {idxs = _ -, _} zero x = ε -, x
only {idxs = _ -, _} (suc i) x = only i x -, ℓ∅

channel-ℓ# : {idxs : Idxs n} (c : Channel n) → Ctx idxs
channel-ℓ# internal = ε
channel-ℓ# (external x) = only x ℓ#

∋-I : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : (Carrier idx) ²}
    → γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ
    → idx ≡ Vec.lookup idxs i
∋-I zero = refl
∋-I (suc x) = ∋-I x

∋-t : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : (Carrier idx) ²}
    → γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ
    → t ≡ Vec.lookup γ i
∋-t zero = refl
∋-t (suc a) = ∋-t a

∋-⊎ : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : Carrier idx ²}
    → (x : γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ)
    → Γ ≔ only i (subst (λ i → Carrier i ²) (∋-I x) c) ⊎ Ξ
∋-⊎ (zero ⦃ check ⦄) = ⊎-idˡ _ , proj₂ (toWitness check)
∋-⊎ (suc x) = ∋-⊎ x , ∙²-idˡ _

lookup-only : {idxs : Idxs n} (i : Fin n) {c : (Carrier (Vec.lookup idxs i)) ²}
            → All.lookup i (only {idxs = idxs} i c) ≡ c
lookup-only {idxs = _ -, _} zero = refl
lookup-only {idxs = _ -, _} (suc i) = lookup-only i

only-∙ : {idxs : Idxs n}
       → (i : Fin n)
       → {x y z : (Carrier (Vec.lookup idxs i)) ²}
       → x ≔ y ∙² z
       → only {idxs = idxs} i x ≔ only i y ⊎ only i z
only-∙ {idxs = _ -, _} zero s = ⊎-idˡ _ , s
only-∙ {idxs = _ -, _} (suc i) s = only-∙ i s , ∙²-idˡ _

subst-idx : ∀ {idx idx'} {eq : idx ≡ idx'} → (δ : ∀ {idx} → (Carrier idx) ²) → subst (λ i → Carrier i ²) eq δ ≡ δ
subst-idx {eq = refl} δ = refl

∋-∙ : {γ : PreCtx n} {idx : Idx} {idxs : Idxs n} {Γ Ξ : Ctx idxs} (c : ∀ {idx} → (Carrier idx) ²)
    → (x : γ ∝ Γ [ i ]≔ t ∝ c {idx} ⊠ Ξ)
    → All.lookup i Γ ≔ c ∙² All.lookup i Ξ
∋-∙ {i = i} {Γ = Γ} {Ξ = Ξ} c x = subst (λ ● → All.lookup i Γ ≔ ● ∙² All.lookup i Ξ)
                                        (trans (lookup-only i) (subst-idx c))
                                        (⊎-get i (∋-⊎ x))

⊢-⊎ : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} → γ ∝ Γ ⊢ P ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
⊢-⊎ end = ε , ⊎-idˡ _
⊢-⊎ (chan t m μ ⊢P) = let _ , Γ≔ = ⊢-⊎ ⊢P
                       in _ , ⊎-tail Γ≔
⊢-⊎ (recv x ⊢P) = let x≔ = ∋-⊎ x
                      _ , P≔ = ⊢-⊎ ⊢P
                   in _ , ⊎-trans x≔ (⊎-tail P≔)
⊢-⊎ (send x y ⊢P) = let x≔ = ∋-⊎ x
                        y≔ = ∋-⊎ y
                        _ , P≔ = ⊢-⊎ ⊢P
                     in _ , ⊎-trans (⊎-trans x≔ y≔) P≔
⊢-⊎ (comp ⊢P ⊢Q) = let _ , P≔ = ⊢-⊎ ⊢P
                       _ , Q≔ = ⊢-⊎ ⊢Q
                    in _ , ⊎-trans P≔ Q≔

∋-0∙ : {Γ Δ : Ctx idxs} → γ ∝ Γ [ i ]≔ t ∝ (0∙ {idx} , 0∙) ⊠ Δ → Γ ≡ Δ
∋-0∙ (zero ⦃ check ⦄) = _-,_ & refl ⊗ ∙²-unique (proj₂ (toWitness check)) (∙²-idˡ _)
∋-0∙ (suc x) = _-,_ & ∋-0∙ x ⊗ refl

mult-insert : (i : Fin (suc n)) → (Carrier idx) ² → Ctx idxs → Ctx (Vec.insert idxs i idx)
mult-insert zero xs' Γ = Γ -, xs'
mult-insert (suc i) xs' (Γ -, xs) = mult-insert i xs' Γ -, xs

mult-remove : Ctx idxs → (i : Fin (suc n)) → Ctx (Vec.remove idxs i)
mult-remove (Γ -, _) zero = Γ
mult-remove (Γ -, ys -, xs) (suc i) = mult-remove (Γ -, ys) i -, xs

mult-update : (i : Fin n) → (Carrier (Vec.lookup idxs i)) ² → Ctx idxs → Ctx idxs
mult-update zero m' (ms -, m) = ms -, m'
mult-update (suc i) m' (ms -, m) = mult-update i m' ms -, m
