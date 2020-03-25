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
    idxs : Vec I n
    γ : PreCtx n
    idx idx' : I
    t : Type
    P Q : Scoped n

only : {idxs : Vec I n} (i : Fin n) → Cs (Vec.lookup idxs i) → Ctx idxs
only {idxs = _ -, _} zero x = ε -, x
only {idxs = _ -, _} (suc i) x = only i x -, 0∙

channel-1∙ : {idxs : Vec I n} (c : Channel n) → Ctx idxs
channel-1∙ internal = ε
channel-1∙ (external x) = only x 1∙

∋-I : {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ : Ctx idxs} {c : Cs idx}
    → (x : γ ∝ Γ ∋ t ∝ c ⊠ Ξ)
    → idx ≡ Vec.lookup idxs (toFin x)
∋-I zero = refl
∋-I (suc x) = ∋-I x

{-
∋-type : {idxs : Vec I n} {Γ Δ : Ctx idxs} {m : Cs idx}
       → (x : γ ∝ Γ ∋ t ∝ m ⊠ Δ) → t ≡ Vec.lookup γ (toFin x) ≡ t
∋-type zero = refl
∋-type (suc x) = ∋-type x
-}

∋-⊎ : {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ : Ctx idxs} {c : Cs idx}
    → (x : γ ∝ Γ ∋ t ∝ c ⊠ Ξ)
    → Γ ≔ only (toFin x) (subst Cs (∋-I x) c) ⊎ Ξ
∋-⊎ (zero {check = check}) = ⊎-idˡ _ , proj₂ (toWitness check)
∋-⊎ (suc x) = ∋-⊎ x , ∙-idˡ _

lookup-only : {idxs : Vec I n} (i : Fin n) {c : Cs (Vec.lookup idxs i)}
            → All.lookup i (only {idxs = idxs} i c) ≡ c
lookup-only {idxs = _ -, _} zero = refl
lookup-only {idxs = _ -, _} (suc i) = lookup-only i

only-∙ : {idxs : Vec I n}
       → (i : Fin n)
       → {x y z : Cs (Vec.lookup idxs i)}
       → x ≔ y ∙ z
       → only {idxs = idxs} i x ≔ only i y ⊎ only i z
only-∙ {idxs = _ -, _} zero s = ⊎-idˡ _ , s
only-∙ {idxs = _ -, _} (suc i) s = only-∙ i s , ∙-idˡ _

subst-idx : ∀ {idx idx'} {eq : idx ≡ idx'} → (δ : ∀ {idx} → Cs idx) → subst Cs eq δ ≡ δ
subst-idx {eq = refl} δ = refl

∋-∙ : {γ : PreCtx n} {idx : I} {idxs : Vec I n} {Γ Ξ : Ctx idxs} (c : ∀ {idx} → Cs idx)
    → (x : γ ∝ Γ ∋ t ∝ c {idx} ⊠ Ξ)
    → All.lookup (toFin x) Γ ≔ c ∙ All.lookup (toFin x) Ξ
∋-∙ {Γ = Γ} {Ξ = Ξ} c x = subst (λ ● → All.lookup (toFin x) Γ ≔ ● ∙ All.lookup (toFin x) Ξ)
                                (trans (lookup-only (toFin x)) (subst-idx c))
                                (⊎-get (toFin x) (∋-⊎ x))

⊢-⊎ : {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ : Ctx idxs} → γ ∝ Γ ⊢ P ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
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

∋-0∙ : {Γ Δ : Ctx idxs} → γ ∝ Γ ∋ t ∝ 0∙ {idx} ⊠ Δ → Γ ≡ Δ
∋-0∙ (zero {check = check}) = _-,_ & refl ⊗ ∙-unique (proj₂ (toWitness check)) (∙-idˡ _)
∋-0∙ (suc x) = _-,_ & ∋-0∙ x ⊗ refl

mult-insert : (i : Fin (suc n)) → Cs idx → Ctx idxs → Ctx (Vec.insert idxs i idx)
mult-insert zero xs' Γ = Γ -, xs'
mult-insert (suc i) xs' (Γ -, xs) = mult-insert i xs' Γ -, xs

mult-remove : Ctx idxs → (i : Fin (suc n)) → Ctx (Vec.remove idxs i)
mult-remove (Γ -, _) zero = Γ
mult-remove (Γ -, ys -, xs) (suc i) = mult-remove (Γ -, ys) i -, xs

mult-update : (i : Fin n) → Cs (Vec.lookup idxs i) → Ctx idxs → Ctx idxs
mult-update zero m' (ms -, m) = ms -, m'
mult-update (suc i) m' (ms -, m) = mult-update i m' ms -, m
