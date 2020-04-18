open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to hrefl; sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)
open import Relation.Nullary using (yes; no)
open import Function.Reasoning
open import Function using (_∘_)

import Data.Empty as Empty
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Nat.Base as Nat
import Data.Vec.Base as Vec
import Data.Vec.Properties as Vecₚ
import Data.Fin.Base as Fin
import Data.Fin.Properties as Finₚ
import Data.Vec.Relation.Unary.All as All

open Empty using (⊥-elim)
open Unit using (tt)
open Nat using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Substitution (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem.Framing Ω

private
  variable
    n : ℕ
    i j : Fin n
    t t' : Type
    γ : PreCtx n
    idx : Idx
    idxs : Idxs n
    x m m' l δ : Carrier idx ²
    Γ Γₗ Γᵣ Ξₗ Ξᵣ Δ Δ' Ξ' Θ Ψ Ξ Ψ' Θ' Δₗ Δᵣ Β : Ctx idxs
    P : Scoped n

≡-Only-⊎ : {idxs : Idxs n} {Γ xati : Ctx idxs}
          → (i : Fin n)
          → All.lookup i Γ ≡ All.lookup i xati
          → xati ≔ x at i ⊠ ε {idxs = idxs}
          → Σ[ Δ ∈ Ctx idxs ]
            (Γ ≔ Δ ⊎ xati × All.lookup i Δ ≡ ℓ∅)

≡-Only-⊎ {Γ = _ -, _} zero refl (zero x) = _ , (⊎-idʳ , ∙²-idˡ) , refl
≡-Only-⊎ {Γ = _ -, _} (suc i) eq (suc xati) with ≡-Only-⊎ i eq xati
≡-Only-⊎ {Γ = _ -, _} (suc i) eq (suc xati) | _ , Γ≔ , eq' = _ , (Γ≔ , ∙²-idʳ) , eq'

diff : {x y : Carrier idx ²}
     → Γ ≔ x at i ⊠ Ξ
     → Ξ ≔ Δ ⊎ Ψ
     → All.lookup i Δ ≡ ℓ∅
     → Γ ≔ y at i ⊠ Θ
     → Θ ≔ Β ⊎ Ψ
     → ∃[ z ] (x ≔ y ∙² z)

diff (zero x) (_ , Ξ≔) refl (zero y) (_ , Θ≔)
  rewrite ∙²-unique Ξ≔ ∙²-idˡ =
  let _ , a , b = ∙²-assoc⁻¹ y Θ≔
  in _ , subst (λ ● → ● ≔ _ ∙² _) (∙²-uniqueˡ a x) b
diff (suc x) (Ξ≔ , _) eq (suc y) (Θ≔ , _) = diff x Ξ≔ eq y Θ≔

split : {x y z : Carrier idx ²}
      → x ≔ y ∙² z
      → Γ ≔ x at i ⊠ Ξ
      → ∃[ Δ ] (Γ ≔ y at i ⊠ Δ × Δ ≔ z at i ⊠ Ξ)
split s (zero x) = let _ , x' , s' = ∙²-assoc x s in _ , zero x' , zero s'
split s (suc x) with split s x
split s (suc x) | _ , y , z = _ , suc y , suc z

bar : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Γᵢ Γⱼ Δ Ψ : Ctx idxs} {i j : Fin n} {m : Carrier idx ²}
    → γ ∝ Γᵢ [ i ]≔ t ∝ m ⊠ Γ
    → γ ∝ Γⱼ [ j ]≔ t ∝ m ⊠ Γ
    → i Fin.≤ j
    → All.lookup i Δ ≡ ℓ∅
    → Γ ≔ Δ ⊎ Ψ
    → γ ∝ Γᵢ ⊢ P ⊠ Ψ
    → γ ∝ Γⱼ ⊢ [ j / i ] P ⊠ Ψ
bar ∋i ∋j i≤j eq Γ≔ end with ∋-⊎ ∋i
bar ∋i ∋j i≤j eq Γ≔ end | _ , Γᵢ≔m∙Γ
  rewrite ⊎-mut-cancel Γ≔ Γᵢ≔m∙Γ | Only-≡ℓ∅ (∋-Only ∋i) | Only-ℓ∅-≡ (∋-Only ∋j) = end
bar ∋i ∋j i≤j eq Γ≔ (chan t m μ ⊢P) = chan t m μ (bar (suc ∋i) (suc ∋j) (Nat.s≤s i≤j) eq (Γ≔ , ∙²-idʳ) ⊢P)
bar {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = x} ∋x ⊢P) with ∋-≡Idx ∋i | ∋-≡Idx ∋x | ⊢-⊎ ⊢P | i Finₚ.≟ x
bar {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = .i} ∋x ⊢P) | refl | refl | (_ -, _) , (⊢P≔ , _) | yes refl =
  let
    typecheck = trans (∋-≡Type ∋j) (trans (sym (∋-≡Type ∋i)) (∋-≡Type ∋x))
    δ , m≔ℓᵢ∙δ = diff (∋-Only ∋i) Γ≔ eq (∋-Only ∋x) ⊢P≔
    Ξⱼ , Γⱼ≔ℓᵢ∙Ξⱼ , Ξⱼ≔δ∙Γ = split m≔ℓᵢ∙δ (∋-Only ∋j)
    Ξᵢ , Γᵢ≔ℓᵢ∙Ξᵢ , Ξᵢ≔δ∙Γ = split m≔ℓᵢ∙δ (∋-Only ∋i)
    Γᵢ≔ℓᵢ∙Ξₓ = ∋-Only ∋x
    Ξₓ≡Ξᵢ = Only-uniqueʳ Γᵢ≔ℓᵢ∙Ξᵢ Γᵢ≔ℓᵢ∙Ξₓ
    Ξₓ≔δ∙Γ = subst (λ ● → ● ≔ δ at _ ⊠ _) Ξₓ≡Ξᵢ Ξᵢ≔δ∙Γ
  in recv (Only-∋ Γⱼ≔ℓᵢ∙Ξⱼ typecheck)
  (bar (suc (Only-∋ Ξₓ≔δ∙Γ (∋-≡Type ∋i)))
       (suc (Only-∋ Ξⱼ≔δ∙Γ (∋-≡Type ∋j)))
       (Nat.s≤s i≤j) eq (Γ≔ , ∙²-idʳ) ⊢P)

bar {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = x} ∋x ⊢P) | refl | refl | (_ -, _) , (⊢P≔ , _) | no ¬p =
  let
    Δi , Γᵢ≔Δi∙Ξ , Δi≔ℓᵢ = Only-⊎ (∋-Only ∋x)
  in
  recv (∋-frame Γᵢ≔Δi∙Ξ {!∋x!} ∋x) {!!}
bar ∋i ∋j i≤j eq Γ≔ (send ∋x ∋y ⊢P) = {!!}
bar ∋i ∋j i≤j eq Γ≔ (comp ⊢P ⊢Q) = {! !}

switch : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Carrier idx ²}
       → γ -, t ∝ Γ -, m ⊢ P ⊠ Ψ -, ℓ∅
       → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
       → ∃[ Θ ] (γ      ∝ Γ      [ j ]≔ t ∝ m ⊠ Θ
               × γ -, t ∝ Θ -, m ⊢ P          ⊠ Ξ -, ℓ∅)
switch ⊢P ∋j with ⊢-⊎ ⊢P | ∋-⊎ ∋j
switch ⊢P ∋j | (Δ⊢P -, _) , (Γ≔ , _) | Δj , Ψ≔ =
  let W , Γ≔Δj∙W , W≔Δ⊢P∙Ξ = ⊎-assoc (⊎-comm Γ≔) Ψ≔ in
  _ , ∋-frame Ψ≔ Γ≔Δj∙W  ∋j , ⊢-frame (Γ≔ , ∙²-idʳ) (⊎-comm W≔Δ⊢P∙Ξ , ∙²-idʳ) ⊢P

⊢-subst' : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Carrier idx ²}
         → γ -, t ∝ Γ -, m ⊢ P ⊠ Ψ -, ℓ∅
         → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
         → γ -, t ∝ Γ -, m ⊢ [ suc j / zero ] P ⊠ Ξ -, m
⊢-subst' {Γ = Γ} {Ξ} ⊢P y with switch ⊢P y
⊢-subst' {Γ = Γ} {Ξ} ⊢P y | Θ , y' , ⊢P' with ⊢-⊎ ⊢P'
⊢-subst' {Γ = Γ} {Ξ} ⊢P y | Θ , y' , ⊢P' | (_ -, _) , (⊢P'≔ , _) =
  ⊢-frame (proj₂ Γ≔ , ∙²-idˡ) (proj₂ Γ≔ , ∙²-idˡ) ⊢P''
  where
  ⊢P'' = bar (Only-∋ (zero ∙²-idʳ) refl) (suc y') Nat.z≤n refl (⊢P'≔ , ∙²-idʳ) ⊢P'
  Γ≔ : ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
  Γ≔ with ⊢-⊎ ⊢P''
  Γ≔ | (_ -, _) , (x , _) = _ , x

postulate
  {- TARGET -}
  ⊢-subst : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t t'} {idx idx'}  {m : Carrier idx ²} {m' : Carrier idx' ²}
          → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
          → γ -, t' ∝ Γ -, m' ⊢ P ⊠ Ψ -, ℓ∅
          → γ -, t' ∝ Γ -, m' ⊢ [ suc j / zero ] P ⊠ Ξ -, m'
 
