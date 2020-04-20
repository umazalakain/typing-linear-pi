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
    x y z m m' l δ : Carrier idx ²
    Γ Γₗ Γᵣ Ξₗ Ξᵣ Δ Δ' Ξ' Θ Ψ Ξ Ψ' Θ' Δₗ Δᵣ Β : Ctx idxs
    P : Scoped n

diff : Γ ≔ x at i ⊠ Ξ
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


split : x ≔ y ∙² z
      → Γ ≔ x at i ⊠ Ξ
      → ∃[ Δ ] (Γ ≔ y at i ⊠ Δ × Δ ≔ z at i ⊠ Ξ)
split s (zero x) = let _ , x' , s' = ∙²-assoc x s in _ , zero x' , zero s'
split s (suc x) with split s x
split s (suc x) | _ , y , z = _ , suc y , suc z

jump : {Γ Ψ Δ Ξ : Ctx idxs}
     → Γ ≔ x at i ⊠ Ψ
     → Δ ≔ y at j ⊠ ε
     → i ≢ j
     → Γ ≔ Δ ⊎ Ξ
     → Σ[ Θ ∈ Ctx idxs ] (Ψ ≔ Δ ⊎ Θ)
jump (zero x) (zero y) i≢j Γ≔ = ⊥-elim (i≢j refl)
jump (zero x) (suc ∋j) i≢j (Γ≔ , x≔) = _ , (Γ≔ , ∙²-idˡ)
jump (suc ∋i) (zero y) i≢j (Γ≔ , x≔) = _ , (⊎-idˡ , x≔)
jump (suc ∋i) (suc ∋j) i≢j (Γ≔ , x≔) with jump ∋i ∋j (i≢j ∘ cong suc) Γ≔
jump (suc ∋i) (suc ∋j) i≢j (Γ≔ , x≔) | _ , Γ'≔ = (_ -, _) , (Γ'≔ , ∙²-idˡ)

center : {Γₗ Γᵣ Γ Δₗ Δᵣ Ψ : Ctx idxs}
       → i ≢ j
       → Γₗ ≔ x at i ⊠ Γ
       → Γᵣ ≔ y at j ⊠ Γ
       → Γₗ ≔ Δₗ ⊎ Ψ
       → Γᵣ ≔ Δᵣ ⊎ Ψ
       → Σ[ Δ ∈ Ctx idxs ] (Γ ≔ Δ ⊎ Ψ)
center i≢j (zero _) (zero _)  Γₗ Γᵣ = ⊥-elim (i≢j refl)
center i≢j (zero _) (suc _)  (Γₗ , l) (Γᵣ , r) = _ , (Γₗ , r)
center i≢j (suc _)  (zero _) (Γₗ , l) (Γᵣ , r) = _ , (Γᵣ , l)
center i≢j (suc ∋i) (suc ∋j) (Γₗ , _) (Γᵣ , _) with center (i≢j ∘ cong suc) ∋i ∋j Γₗ Γᵣ
center i≢j (suc ∋i) (suc ∋j) (Γₗ , l) (Γᵣ , _) | _ , Γ = (_ -, _) , (Γ , l)

postulate
  TODO : ∀ {a} {A : Set a} → A

⊢-subst-ih : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Γᵢ Γⱼ Δ Ψ : Ctx idxs} {i j : Fin n} {m : Carrier idx ²}
           → γ ∝ Γᵢ [ i ]≔ t ∝ m ⊠ Γ
           → γ ∝ Γⱼ [ j ]≔ t ∝ m ⊠ Γ
           → i Fin.≤ j -- TODO: we don't need this
           → All.lookup i Δ ≡ ℓ∅
           → Γ ≔ Δ ⊎ Ψ
           → γ ∝ Γᵢ ⊢ P ⊠ Ψ
           → γ ∝ Γⱼ ⊢ [ j / i ] P ⊠ Ψ

⊢-subst-ih ∋i ∋j i≤j eq Γ≔ end with ∋-⊎ ∋i
⊢-subst-ih ∋i ∋j i≤j eq Γ≔ end | _ , Γᵢ≔m∙Γ
  rewrite ⊎-mut-cancel Γ≔ Γᵢ≔m∙Γ | Only-≡ℓ∅ (∋-Only ∋i) | Only-ℓ∅-≡ (∋-Only ∋j) = end
⊢-subst-ih ∋i ∋j i≤j eq Γ≔ (chan t m μ ⊢P) = chan t m μ (⊢-subst-ih (suc ∋i) (suc ∋j) (Nat.s≤s i≤j) eq (Γ≔ , ∙²-idʳ) ⊢P)
⊢-subst-ih {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = x} ∋x ⊢P) with ∋-≡Idx ∋i | ∋-≡Idx ∋x | ⊢-⊎ ⊢P | i Finₚ.≟ x
⊢-subst-ih {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = .i} ∋x ⊢P) | refl | refl | (_ -, _) , (⊢P≔ , _) | yes refl =
  let
    typecheck = trans (∋-≡Type ∋j) (trans (sym (∋-≡Type ∋i)) (∋-≡Type ∋x))
    δ , m≔ℓᵢ∙δ = diff (∋-Only ∋i) Γ≔ eq (∋-Only ∋x) ⊢P≔
    Ξⱼ , Γⱼ≔ℓᵢ∙Ξⱼ , Ξⱼ≔δ∙Γ = split m≔ℓᵢ∙δ (∋-Only ∋j)
    Ξᵢ , Γᵢ≔ℓᵢ∙Ξᵢ , Ξᵢ≔δ∙Γ = split m≔ℓᵢ∙δ (∋-Only ∋i)
    Γᵢ≔ℓᵢ∙Ξₓ = ∋-Only ∋x
    Ξₓ≡Ξᵢ = Only-uniqueʳ Γᵢ≔ℓᵢ∙Ξᵢ Γᵢ≔ℓᵢ∙Ξₓ
    Ξₓ≔δ∙Γ = subst (λ ● → ● ≔ δ at _ ⊠ _) Ξₓ≡Ξᵢ Ξᵢ≔δ∙Γ
  in recv (Only-∋ Γⱼ≔ℓᵢ∙Ξⱼ typecheck)
  (⊢-subst-ih (suc (Only-∋ Ξₓ≔δ∙Γ (∋-≡Type ∋i)))
       (suc (Only-∋ Ξⱼ≔δ∙Γ (∋-≡Type ∋j)))
       (Nat.s≤s i≤j) eq (Γ≔ , ∙²-idʳ) ⊢P)

⊢-subst-ih {i = i} ∋i ∋j i≤j eq Γ≔Δ∙Ψ (recv {i = x} ∋x ⊢P) | refl | refl | (_ -, _) , (⊢P≔ , _) | no i≢x =
  --    Γi -- Δx --> Ξx------
  --    |            .       \
  --   Δi           Δi        \ ⊢ P
  --    |            ·         \
  --    v            v         |
  --    Γ ··· Δx ··> Θ·····Δ'  |
  --    ^\           ^      \  |
  --    | \         Δj       \ |
  --    |  \         ·        \|
  --    |   Δ--------+---------Ψ
  --   Δj            ·         | ⊢ P [ j / i]
  --    |            ·         |
  --    Γj -- Δx --> Ξj----·   |
  --                        \  |
  --                         \ |
  --                          \|
  let
    Δx , Γi≔Δx∙Ξx , Δx≔ℓᵢ = Only-⊎ (∋-Only ∋x)
    Δi , Γi≔Δi∙Γ , Δi≔ℓᵢ = Only-⊎ (∋-Only ∋i)
    Δj , Γj≔Δj∙Γ , Δj≔ℓᵢ = Only-⊎ (∋-Only ∋j)
    Θ  , Γ≔Δx∙Θ = jump (∋-Only ∋i) Δx≔ℓᵢ i≢x Γi≔Δx∙Ξx
    Θ' , Ξx≔Δi∙Θ' = jump (∋-Only ∋x) Δi≔ℓᵢ (i≢x ∘ sym) Γi≔Δi∙Γ
    Ξj , Γj≔Δx∙Ξj , Ξj≔Θ∙Δj = ⊎-assoc (⊎-comm Γj≔Δj∙Γ) Γ≔Δx∙Θ
    _ , Γi≔ΔxΔi∙Θ' , ΔxΔi≔Δx∙Δi = ⊎-assoc⁻¹ Γi≔Δx∙Ξx Ξx≔Δi∙Θ'
    _ , Γi≔ΔiΔx∙Θ , ΔiΔx≔Δi∙Δx = ⊎-assoc⁻¹ Γi≔Δi∙Γ Γ≔Δx∙Θ
    _ , Γj≔ΔjΔ∙Ψ , ΔjΔ≔Δj∙Δ = ⊎-assoc⁻¹ Γj≔Δj∙Γ Γ≔Δ∙Ψ
    ΔxΔi≡ΔiΔx = ⊎-unique ΔxΔi≔Δx∙Δi (⊎-comm ΔiΔx≔Δi∙Δx)
    Γi≔ΔiΔx∙Θ' = subst (λ ● → _ ≔ ● ⊎ Θ') ΔxΔi≡ΔiΔx Γi≔ΔxΔi∙Θ'
    Θ'≡Θ = ⊎-uniqueˡ (⊎-comm Γi≔ΔiΔx∙Θ') (⊎-comm Γi≔ΔiΔx∙Θ)
    Ξx≔Δi∙Θ = subst (λ ● → _ ≔ _ ⊎ ●) Θ'≡Θ Ξx≔Δi∙Θ'
    ∋i' = ⊎-Only Ξx≔Δi∙Θ Δi≔ℓᵢ
    ∋j' = ⊎-Only (⊎-comm Ξj≔Θ∙Δj) Δj≔ℓᵢ
    ∋x' = ∋-frame Γi≔Δx∙Ξx Γj≔Δx∙Ξj ∋x
    Δ' , Θ≔Δ'∙Ψ = center i≢x ∋i' (⊎-Only Γ≔Δx∙Θ Δx≔ℓᵢ) ⊢P≔ Γ≔Δ∙Ψ
    Γ[i]≡Θ[i] = Only-lookup-≢ (⊎-Only Γ≔Δx∙Θ Δx≔ℓᵢ) i (i≢x ∘ sym)
    Δ'[i]≡Δ[i] = ∙²-uniqueˡ (⊎-get i Θ≔Δ'∙Ψ) (subst (λ ● → ● ≔ _ ∙² _) Γ[i]≡Θ[i] (⊎-get i Γ≔Δ∙Ψ))
  in
  recv ∋x'
       (⊢-subst-ih (suc (Only-∋ ∋i' (∋-≡Type ∋i)))
                   (suc (Only-∋ ∋j' (∋-≡Type ∋j)))
                   (Nat.s≤s i≤j) (trans Δ'[i]≡Δ[i] eq) (Θ≔Δ'∙Ψ , ∙²-idʳ) ⊢P)

⊢-subst-ih ∋i ∋j i≤j eq Γ≔ (send ∋x ∋y ⊢P) = TODO
⊢-subst-ih ∋i ∋j i≤j eq Γ≔ (comp ⊢P ⊢Q) = TODO 

switch : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Carrier idx ²}
       → γ -, t ∝ Γ -, m ⊢ P ⊠ Ψ -, ℓ∅
       → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
       → ∃[ Θ ] (γ      ∝ Γ      [ j ]≔ t ∝ m ⊠ Θ
               × γ -, t ∝ Θ -, m ⊢ P          ⊠ Ξ -, ℓ∅)
switch ⊢P ∋j with ⊢-⊎ ⊢P | ∋-⊎ ∋j
switch ⊢P ∋j | (Δ⊢P -, _) , (Γ≔ , _) | Δj , Ψ≔ =
  let W , Γ≔Δj∙W , W≔Δ⊢P∙Ξ = ⊎-assoc (⊎-comm Γ≔) Ψ≔ in
  _ , ∋-frame Ψ≔ Γ≔Δj∙W  ∋j , ⊢-frame (Γ≔ , ∙²-idʳ) (⊎-comm W≔Δ⊢P∙Ξ , ∙²-idʳ) ⊢P


⊢-subst : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Carrier idx ²}
        → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
        → γ -, t ∝ Γ -, m ⊢ P ⊠ Ψ -, ℓ∅
        → γ -, t ∝ Γ -, m ⊢ [ suc j / zero ] P ⊠ Ξ -, m
⊢-subst {Γ = Γ} {Ξ} y ⊢P with switch ⊢P y
⊢-subst {Γ = Γ} {Ξ} y ⊢P | Θ , y' , ⊢P' with ⊢-⊎ ⊢P'
⊢-subst {Γ = Γ} {Ξ} y ⊢P | Θ , y' , ⊢P' | (_ -, _) , (⊢P'≔ , _) =
  ⊢-frame (proj₂ Γ≔ , ∙²-idˡ) (proj₂ Γ≔ , ∙²-idˡ) ⊢P''
  where
  ⊢P'' = ⊢-subst-ih (Only-∋ (zero ∙²-idʳ) refl) (suc y') Nat.z≤n refl (⊢P'≔ , ∙²-idʳ) ⊢P'
  Γ≔ : ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
  Γ≔ with ⊢-⊎ ⊢P''
  Γ≔ | (_ -, _) , (x , _) = _ , x
