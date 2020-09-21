{-# OPTIONS --safe #-} -- --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
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
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem.Algebras

module PiCalculus.LinearTypeSystem.Substitution (Ω : Algebras) where
open Algebras Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem.Framing Ω

private
  variable
    n : ℕ
    i j : Fin n
    t t' : Type
    γ : PreCtx n
    idx idx' : Idx
    idxs : Idxs n
    x y z m m' l δ : Usage idx ²
    Γ Γₗ Γᵣ Ξₗ Ξᵣ Δ Δ' Ξ' Θ Ψ Ξ Ψ' Θ' Δₗ Δᵣ Β : Ctx idxs
    P : Scoped n

midpoint : {Γᵢ Γ Δ Ψ ΔP Ξᵢ ΔQ Ψᵢ : Ctx idxs} {m n : Usage idx ²}
         → Γᵢ ∋[ i ] m ▹ Γ
         → Γ ≔ Δ ⊗ Ψ
         → All.lookup i Δ ≡ ℓ∅
         → Γᵢ ≔ ΔP ⊗ Ξᵢ
         → Ξᵢ ≔ ΔQ ⊗ Ψᵢ
         → Ψᵢ ∋[ i ] n ▹ Ψ
         → Σ[ δ ∈ Usage idx ² ]
           Σ[ Θ ∈ Ctx idxs ]
           Σ[ Δ₁ ∈ Ctx idxs ]
           Σ[ Δ₂ ∈ Ctx idxs ] (
           Ξᵢ ∋[ i ] δ ▹ Θ
         × Γ ≔ Δ₁ ⊗ Θ
         × Θ ≔ Δ₂ ⊗ Ψ)

midpoint {i = zero} (zero γᵢ≔m∙γ) (Γ≔Δ∙Ψ , γ≔δ∙ψ) refl (Γᵢ≔ΔP∙Ξᵢ , γᵢ≔δp∙ξᵢ) (Ξᵢ≔ΔQ∙Ψᵢ , ξᵢ≔δq∙ψᵢ) (zero ψᵢ≔n∙ψ)
  rewrite ∙²-unique γ≔δ∙ψ ∙²-idˡ =
  let _ , ξᵢ≔δ∙θ , _ = ∙²-assoc⁻¹ ξᵢ≔δq∙ψᵢ ψᵢ≔n∙ψ in
  _ , _ , (_ -, _) , _ , zero ξᵢ≔δ∙θ , (Γᵢ≔ΔP∙Ξᵢ , ∙²-idˡ) , (Ξᵢ≔ΔQ∙Ψᵢ , ∙²-idˡ)
midpoint {i = suc i} (suc Γᵢ≔m∙Γ) (Γ≔Δ∙Ψ , _) Δ[i]≡ℓ∅ (Γᵢ≔ΔP∙Ξᵢ , γᵢ≔δp∙ξᵢ) (Ξᵢ≔ΔQ∙Ψᵢ , ξᵢ≔δq∙ψᵢ) (suc ψᵢ≔n∙ψ) =
  let _ , _ , _ , _ , Ξᵢ≔δ∙Θ , Γ≔Δ₁∙Θ , Θ≔Δ₂∙Ψ = midpoint Γᵢ≔m∙Γ Γ≔Δ∙Ψ Δ[i]≡ℓ∅ Γᵢ≔ΔP∙Ξᵢ Ξᵢ≔ΔQ∙Ψᵢ ψᵢ≔n∙ψ in
  _ , _ , (_ -, _) , _ , suc Ξᵢ≔δ∙Θ , (Γ≔Δ₁∙Θ , γᵢ≔δp∙ξᵢ) , (Θ≔Δ₂∙Ψ , ξᵢ≔δq∙ψᵢ)

cutpoint : {Γ Δ Θ Γⱼ : Ctx idxs} {m n l : Usage idx ²}
       → Γ ≔ Δ ⊗ Θ
       → Γⱼ ∋[ j ] m ▹ Γ
       → m ≔ n ∙² l
       → Σ[ Θⱼ ∈ Ctx idxs ] (Θⱼ ∋[ j ] l ▹ Θ)
cutpoint (_ , γ≔) (zero x) m≔ =
  let
    _ , _ , a = ∙²-assoc x m≔
    _ , _ , c = ∙²-assoc (∙²-comm a) γ≔
  in _ , zero (∙²-comm c)
cutpoint (Γ≔ , _) (suc ∋j) m≔ with cutpoint Γ≔ ∋j m≔
cutpoint (Γ≔ , _) (suc ∋j) m≔ | _ , r = _ , suc r

∋-subst : {Γ Γᵢ Γⱼ Δ Ψ Ψᵢ Ψⱼ Ξᵢ CONT : Ctx idxs} {i j x : Fin n} {mx : Usage idx' ²} {m n : Usage idx ²}
        → Vec.lookup γ i ≡ Vec.lookup γ j
        → Γᵢ ∋[ i ] m ▹ Γ
        → Γⱼ ∋[ j ] m ▹ Γ
        → Ψᵢ ∋[ i ] n ▹ Ψ
        → Ψⱼ ∋[ j ] n ▹ Ψ
        → Γ ≔ Δ ⊗ Ψ
        → All.lookup i Δ ≡ ℓ∅
        → γ ； Γᵢ ∋[ x ] t ； mx ▹ Ξᵢ
        → Ξᵢ ≔ CONT ⊗ Ψᵢ
        → Σ[ Ξⱼ ∈ Ctx idxs ]
          Σ[ Θ ∈ Ctx idxs ]
          Σ[ Δ' ∈ Ctx idxs ]
          Σ[ m' ∈ Usage idx ² ]
         (γ ； Γⱼ ∋[ x [ i ↦ j ]' ] t ； mx ▹ Ξⱼ
        × Ξᵢ ∋[ i ] m' ▹ Θ
        × Ξⱼ ∋[ j ] m' ▹ Θ
        × Θ ≔ Δ' ⊗ Ψ
        × All.lookup i Δ' ≡ ℓ∅)
∋-subst {i = i} {x = x} eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (∋t , ∋x) Ξᵢ≔CONT∙Ψᵢ with i Finₚ.≟ x
∋-subst {i = i} {x = x} eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (∋t , ∋x) Ξᵢ≔CONT∙Ψᵢ | yes refl with ∋-≡Idx ∋i | ∋-≡Idx ∋x
∋-subst {i = i} {x = x} eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (∋t , ∋x) Ξᵢ≔CONT∙Ψᵢ | yes refl | refl | refl =
  let
    _ , Ξᵢ≔CONTn∙Ψ , _ = ⊗-assoc⁻¹ Ξᵢ≔CONT∙Ψᵢ (proj₁ (proj₂ (∋-⊗ ∈i)))
    δ , m≔ℓ∙δ = boil ∋i ∋x Ξᵢ≔CONTn∙Ψ Γ≔Δ∙Ψ Δ∋iℓ∅
    _ , Γᵢ≔ℓ∙⁇ᵢ , ⁇ᵢ≔δ∙Γ = split m≔ℓ∙δ ∋i
    _ , Γⱼ≔ℓ∙⁇ⱼ , ⁇ⱼ≔δ∙Γ = split m≔ℓ∙δ ∋j
    ⁇ᵢ≡Ξᵢ = ∋-uniqueʳ Γᵢ≔ℓ∙⁇ᵢ ∋x
    Ξᵢ≔δ∙Γ = subst (λ ● → ● ∋[ _ ] δ ▹ _) ⁇ᵢ≡Ξᵢ ⁇ᵢ≔δ∙Γ
  in _ , _ , _ , _ , (≡Type-∋ (trans (sym eq) (∋-≡Type ∋t)) , Γⱼ≔ℓ∙⁇ⱼ) , Ξᵢ≔δ∙Γ , ⁇ⱼ≔δ∙Γ , Γ≔Δ∙Ψ , Δ∋iℓ∅

∋-subst {i = i} {x = x} eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (∋t , ∋x) Ξᵢ≔CONT∙Ψᵢ | no i≢x =
  let
    _ , Ξᵢ≔m∙Θ , Γ≔ℓ∙Θ = diamond i≢x ∋x ∋i
    _ , Γⱼ≔m'∙Γ , m'≔m∙ε = ∋-⊗ ∋j
    _ , Γ≔ℓ'∙Θ ,  ℓ'≔ℓ∙ε = ∋-⊗ Γ≔ℓ∙Θ
    _ , Γⱼ≔ℓ'∙Ξⱼ , Ξⱼ≔m'∙Θ = reverse Γⱼ≔m'∙Γ Γ≔ℓ'∙Θ
    _ , Γᵢ≔ℓCONT∙Ψᵢ , _ = ⊗-assoc⁻¹ (proj₁ (proj₂ (∋-⊗ ∋x))) Ξᵢ≔CONT∙Ψᵢ
    _ , Ξᵢ≔CONTn∙Ψ , _ = ⊗-assoc⁻¹ Ξᵢ≔CONT∙Ψᵢ (proj₁ (proj₂ (∋-⊗ ∈i)))
    _ , Θ≔Δ'∙Ψ = outer-diamond i≢x ∋i ∋x Γ≔ℓ∙Θ Ξᵢ≔m∙Θ Γ≔Δ∙Ψ Ξᵢ≔CONTn∙Ψ
    _ , Δ'∋iℓ∅ = split-ℓ∅ Γ≔Δ∙Ψ (proj₁ (proj₂ (∋-⊗ Γ≔ℓ∙Θ))) Θ≔Δ'∙Ψ Δ∋iℓ∅
  in _ , _ , _ , _ , (∋t , ⊗-∋ Γⱼ≔ℓ'∙Ξⱼ ℓ'≔ℓ∙ε) , Ξᵢ≔m∙Θ , ⊗-∋ Ξⱼ≔m'∙Θ m'≔m∙ε , Θ≔Δ'∙Ψ , Δ'∋iℓ∅

⊢-subst-ih : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Γᵢ Γⱼ Δ Ψ Ψᵢ Ψⱼ : Ctx idxs} {i j : Fin n} {m n : Usage idx ²}
           → Vec.lookup γ i ≡ Vec.lookup γ j
           → Γᵢ ∋[ i ] m ▹ Γ
           → Γⱼ ∋[ j ] m ▹ Γ
           → Ψᵢ ∋[ i ] n ▹ Ψ
           → Ψⱼ ∋[ j ] n ▹ Ψ
           → Γ ≔ Δ ⊗ Ψ
           → All.lookup i Δ ≡ ℓ∅
           → γ ； Γᵢ ⊢ P ▹ Ψᵢ
           → γ ； Γⱼ ⊢ P [ i ↦ j ] ▹ Ψⱼ

⊢-subst-ih {i = i} eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ 𝟘 with ⊗-get i Γ≔Δ∙Ψ | ∋-≡Idx ∈i | ∋-≡Idx ∋i
⊢-subst-ih {i = i} eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ 𝟘 | Γi≔Δi∙Ψi | refl | refl with ∋-lookup-≡ ∈i | ∋-lookup-≡ ∋i
⊢-subst-ih {i = i} eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ 𝟘 | Γi≔Δi∙Ψi | refl | refl | qeq | qe
  rewrite Δ∋iℓ∅ | ∙²-unique Γi≔Δi∙Ψi ∙²-idˡ | ∙²-uniqueˡ qe qeq | ∋-uniqueʳ ∋i ∈i | ∋-uniqueˡ ∋j ∈j = 𝟘
⊢-subst-ih eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (ν t m μ ⊢P) =
  ν t m μ (⊢-subst-ih eq (suc ∋i) (suc ∋j) (suc ∈i) (suc ∈j) (Γ≔Δ∙Ψ , ∙²-idʳ) Δ∋iℓ∅ ⊢P)
⊢-subst-ih eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (∋x ⦅⦆ ⊢P) with ⊢-⊗ ⊢P
⊢-subst-ih eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (∋x ⦅⦆ ⊢P) | (_ -, _) , (Ξᵢ≔δ⊢P∙Ψᵢ , _) =
  let _ , _ , _ , _ , ∋x' , ∋i' , ∋j' , Θ≔Δ'∙Ψ , Δ'∋iℓ∅ = ∋-subst eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ ∋x Ξᵢ≔δ⊢P∙Ψᵢ in
  ∋x' ⦅⦆ ⊢-subst-ih eq (suc ∋i') (suc ∋j') (suc ∈i) (suc ∈j) (Θ≔Δ'∙Ψ , ∙²-idʳ) Δ'∋iℓ∅ ⊢P
⊢-subst-ih eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ ((∋tx , ∋x) ⟨ ∋ty , ∋y ⟩ ⊢P) =
  let
    _ , δ⊢P = ⊢-⊗ ⊢P
    _ , δy , _ = ∋-⊗ ∋y
    _ , δy⊢P , _ = ⊗-assoc⁻¹ δy δ⊢P
    _ , _ , _ , _ , ∋x' , ∋i' , ∋j' , Θ≔Δ'∙Ψ , Δ'∋iℓ∅ = ∋-subst eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (∋tx , ∋x) δy⊢P
    _ , _ , _ , _ , ∋y' , ∋i'' , ∋j'' , Θ≔Δ''∙Ψ , Δ''∋iℓ∅ = ∋-subst eq ∋i' ∋j' ∈i ∈j Θ≔Δ'∙Ψ Δ'∋iℓ∅ (∋ty , ∋y) δ⊢P
  in ∋x' ⟨ ∋y' ⟩ ⊢-subst-ih eq ∋i'' ∋j'' ∈i ∈j Θ≔Δ''∙Ψ Δ''∋iℓ∅ ⊢P
⊢-subst-ih eq ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (_∥_ {Δ = Ξᵢ} ⊢P ⊢Q) =
  let
    _ , Γᵢ≔δ⊢P∙Ξᵢ = ⊢-⊗ ⊢P
    _ , Ξᵢ≔δ⊢Q∙Ψᵢ = ⊢-⊗ ⊢Q
    _ , _ , _ , _ , Ξᵢ≔δ∙Θ , Γ≔Δ₁∙Θ , Θ≔Δ₂∙Ψ = midpoint ∋i Γ≔Δ∙Ψ Δ∋iℓ∅ Γᵢ≔δ⊢P∙Ξᵢ Ξᵢ≔δ⊢Q∙Ψᵢ ∈i
    _ , Ξᵢ≔δ'∙Θ , δ'≔δ∙ε = ∋-⊗ Ξᵢ≔δ∙Θ
    _ , Γᵢ≔δ'∙⁇ᵢ , ⁇ᵢ≔δ⊢P∙Θ = reverse Γᵢ≔δ⊢P∙Ξᵢ Ξᵢ≔δ'∙Θ
    Δ₁∋iℓ∅ , Δ₂∋iℓ∅ = split-ℓ∅ Γ≔Δ∙Ψ Γ≔Δ₁∙Θ Θ≔Δ₂∙Ψ Δ∋iℓ∅
    _ , m≔δ∙δ⊢P = boil ∋i (⊗-∋ Γᵢ≔δ'∙⁇ᵢ δ'≔δ∙ε) ⁇ᵢ≔δ⊢P∙Θ Γ≔Δ₁∙Θ Δ₁∋iℓ∅
    _ , Ξⱼ≔δ∙Θ = cutpoint Γ≔Δ₁∙Θ ∋j (∙²-comm m≔δ∙δ⊢P)
  in ⊢-subst-ih eq ∋i ∋j Ξᵢ≔δ∙Θ Ξⱼ≔δ∙Θ Γ≔Δ₁∙Θ Δ₁∋iℓ∅ ⊢P ∥ ⊢-subst-ih eq Ξᵢ≔δ∙Θ Ξⱼ≔δ∙Θ ∈i ∈j Θ≔Δ₂∙Ψ Δ₂∋iℓ∅ ⊢Q


switch : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Usage idx ²}
       → γ -, t ； Γ -, m ⊢ P ▹ Ψ -, ℓ∅
       → Ψ ∋[ j ] m ▹ Ξ
       → ∃[ Θ ] (Γ      ∋[ j ] m ▹ Θ
      × γ -, t ； Θ -, m ⊢ P      ▹ Ξ -, ℓ∅)
switch ⊢P ∋j with ⊢-⊗ ⊢P | ∋-⊗ ∋j
switch ⊢P ∋j | (Δ⊢P -, _) , (Γ≔ , _) | _ , Ψ≔ , _ =
  let W , Γ≔Δj∙W , W≔Δ⊢P∙Ξ = ⊗-assoc (⊗-comm Γ≔) Ψ≔ in
  _ , ∋-frame Ψ≔ Γ≔Δj∙W  ∋j , ⊢-frame (Γ≔ , ∙²-idʳ) (⊗-comm W≔Δ⊢P∙Ξ , ∙²-idʳ) ⊢P


⊢-subst : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Usage idx ²}
        → γ ； Ψ ∋[ j ] t ； m ▹ Ξ
        → γ -, t ； Γ -, m ⊢ P ▹ Ψ -, ℓ∅
        → γ -, t ； Γ -, m ⊢ P [ zero ↦ suc j ] ▹ Ξ -, m
⊢-subst {Γ = Γ} {Ξ} (t , y) ⊢P with switch ⊢P y
⊢-subst {Γ = Γ} {Ξ} (t , y) ⊢P | Θ , y' , ⊢P' with ⊢-⊗ ⊢P'
⊢-subst {Γ = Γ} {Ξ} (t , y) ⊢P | Θ , y' , ⊢P' | (_ -, _) , (⊢P'≔ , _) =
  ⊢-frame (proj₂ Γ≔ , ∙²-idˡ) (proj₂ Γ≔ , ∙²-idˡ) ⊢P''
  where
  ⊢P'' = ⊢-subst-ih (sym (∋-≡Type t)) (zero ∙²-idʳ) (suc y') (zero ∙²-idʳ) (suc (∋-ℓ∅ (∋-≡Idx y))) (⊢P'≔ , ∙²-idʳ) refl ⊢P'
  Γ≔ : ∃[ Δ ] (Γ ≔ Δ ⊗ Ξ)
  Γ≔ with ⊢-⊗ ⊢P''
  Γ≔ | (_ -, _) , (x , _) = _ , x
