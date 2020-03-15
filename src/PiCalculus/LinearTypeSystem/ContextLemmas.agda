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
    is : Vec I n
    γ : PreCtx n
    i i' : I
    t : Type
    P Q : Scoped n

∋-∙ : (δ : ∀ {i} → Cs i) {Γ Δ : Ctx is}
    → (x : γ w Γ ∋ t w (δ {i}) ⊠ Δ)
    → All.lookup (toFin x) Γ ≔ (δ {Vec.lookup is (toFin x)}) ∙ All.lookup (toFin x) Δ
∋-∙ δ (zero {check = check}) = proj₂ (toWitness check)
∋-∙ δ (suc x) = ∋-∙ δ x

∋-t : {m : Cs i} {Γ Δ : Ctx is}
    → (x : γ w Γ ∋ t w m ⊠ Δ)
    → Vec.lookup γ (toFin x) ≡ t
∋-t zero = refl
∋-t (suc x) = ∋-t x

C≢B : {t : Type} {m : Cs i} {b : ℕ} → C[ t w m ] ≡ B[ b ] → ⊥
C≢B ()

-- TODO: Δ ≡ x
∋-⊎ : {Γ Ξ : Ctx is} {x : Cs i} → γ w Γ ∋ t w x ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
∋-⊎ (zero {check = check}) = (ε -, _) , ((⊎-idˡ _) , proj₂ (toWitness check))
∋-⊎ (suc i) with ∋-⊎ i
∋-⊎ (suc i) | (Δ , Γ≔) = (Δ -, 0∙) , Γ≔ , (∙-idˡ _)

⊢-⊎ : {Γ Ξ : Ctx is} → γ w Γ ⊢ P ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
⊢-⊎ end = ε , ⊎-idˡ _
⊢-⊎ (chan t m μ ⊢P) = let _ , Γ≔ = ⊢-⊎ ⊢P
                       in _ , ⊎-tail Γ≔
⊢-⊎ (recv x ⊢P) = let _ , x≔ = ∋-⊎ x
                      _ , P≔ = ⊢-⊎ ⊢P
                   in _ , ⊎-trans x≔ (⊎-tail P≔)
⊢-⊎ (send x y ⊢P) = let _ , x≔ = ∋-⊎ x
                        _ , y≔ = ∋-⊎ y
                        _ , P≔ = ⊢-⊎ ⊢P
                     in _ , ⊎-trans (⊎-trans x≔ y≔) P≔
⊢-⊎ (comp ⊢P ⊢Q) = let _ , P≔ = ⊢-⊎ ⊢P
                       _ , Q≔ = ⊢-⊎ ⊢Q
                    in _ , ⊎-trans P≔ Q≔

mult-insert : (i : Fin (suc n)) → Cs i' → Ctx is → Ctx (Vec.insert is i i')
mult-insert zero xs' Γ = Γ -, xs'
mult-insert (suc i) xs' (Γ -, xs) = mult-insert i xs' Γ -, xs

mult-remove : Ctx is → (i : Fin (suc n)) → Ctx (Vec.remove is i)
mult-remove (Γ -, _) zero = Γ
mult-remove (Γ -, ys -, xs) (suc i) = mult-remove (Γ -, ys) i -, xs

mult-update : (i : Fin n) → Cs (Vec.lookup is i) → Ctx is → Ctx is
mult-update zero m' (ms -, m) = ms -, m'
mult-update (suc i) m' (ms -, m) = mult-update i m' ms -, m

_at_ : (∀ {i} → Cs i) → {n : ℕ} → Channel n → {is : Vec I n} → Ctx is
_at_ x internal = ε
_at_ x (external zero) {_ -, _} = ε -, x
_at_ x (external (suc e)) {_ -, _} = (x at (external e)) -, 0∙

lookup-at : ∀ {n} (i : Fin n) {is : Vec I n} {x : ∀ {i} → Cs i}
          → x ≡ All.lookup i (_at_ x (external i) {is})
lookup-at zero {_ -, _} = refl
lookup-at (suc i) {_ -, _} = lookup-at i

∋-at : {Γ Ξ Ξ' : Ctx is} {m : ∀ {i} → Cs i}
     → (x : γ w Γ ∋ t w m {i} ⊠ Ξ)
     → Γ ≔ Ξ' ⊎ (m at (external (toFin x)))
     → Ξ ≡ Ξ'
∋-at {Ξ' = _ -, _} (zero {check = check}) (Γ≔ , s≔) = _-,_
  & ⊎-unique Γ≔ (⊎-idʳ _)
  ⊗ ∙-uniqueˡ (∙-comm (proj₂ (toWitness check))) s≔
∋-at {Ξ' = _ -, _} {m = m} (suc x) (Γ≔ , s≔) = _-,_
  & ∋-at {m = m} x Γ≔
  ⊗ ∙-uniqueˡ (∙-idʳ _) s≔
