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

split : x ≔ y ∙² z
      → Γ ≔ x at i ⊠ Ξ
      → ∃[ Δ ] (Γ ≔ y at i ⊠ Δ × Δ ≔ z at i ⊠ Ξ)
split s (zero x) = let _ , x' , s' = ∙²-assoc x s in _ , zero x' , zero s'
split s (suc x) with split s x
split s (suc x) | _ , y , z = _ , suc y , suc z

postulate
  TODO : ∀ {a} {A : Set a} → A

diff' : {Γₗ Ξₗ Θ Γ Δ : Ctx idxs} {δ⊢p : Carrier idx ²}
      → Γₗ ≔ δ⊢p at i ⊠ Ξₗ
      → Ξₗ ≔ δ at i ⊠ Θ
      → Γₗ ≔ m at i ⊠ Γ
      → Γ ≔ Δ ⊎ Θ
      → All.lookup i Δ ≡ ℓ∅
      → m ≔ δ⊢p ∙² δ
diff' (zero γₗ≔δ⊢P∙ξₗ) (zero ξₗ≔δ∙θ) (zero γₗ≔m∙γ) (_ , γ≔δ∙θ) refl rewrite ∙²-unique γ≔δ∙θ ∙²-idˡ = {!!}
diff' (suc Γₗ≔Δ⊢P∙Ξₗ) (suc Ξₗ≔δ∙Θ) (suc Γₗ≔m∙Γ) (Γ≔Δ∙Θ , _) Δ[i]≡0 = {!!}

diff : {Γₗ Δ⊢P Ξₗ Θ Γ Δ : Ctx idxs}
     → Γₗ ≔ Δ⊢P ⊎ Ξₗ
     → Ξₗ ≔ δ at i ⊠ Θ
     → Γₗ ≔ m at i ⊠ Γ
     → Γ ≔ Δ ⊎ Θ
     → All.lookup i Δ ≡ ℓ∅
     → ∃[ δ⊢p ] (m ≔ δ⊢p ∙² δ × δ⊢p ≅ All.lookup i Δ⊢P)
diff (_ , γₗ≔δ⊢P∙ξₗ) (zero ξₗ≔δ∙θ) (zero γₗ≔m∙γ) (_ , γ≔δ∙θ) refl rewrite ∙²-unique γ≔δ∙θ ∙²-idˡ =
  let
    _ , γₗ≔δ⊢Pδ∙θ , δ⊢Pδ≔δ⊢P∙δ = ∙²-assoc⁻¹ γₗ≔δ⊢P∙ξₗ ξₗ≔δ∙θ
    δ⊢Pδ≡m = ∙²-uniqueˡ γₗ≔δ⊢Pδ∙θ γₗ≔m∙γ
    m≔δ⊢P∙δ = subst (λ ● → ● ≔ _ ∙² _) δ⊢Pδ≡m δ⊢Pδ≔δ⊢P∙δ
  in _ , m≔δ⊢P∙δ , hrefl
diff (Γₗ≔Δ⊢P∙Ξₗ , _) (suc Ξₗ≔δ∙Θ) (suc Γₗ≔m∙Γ) (Γ≔Δ∙Θ , _) Δ[i]≡0 = diff Γₗ≔Δ⊢P∙Ξₗ Ξₗ≔δ∙Θ Γₗ≔m∙Γ Γ≔Δ∙Θ Δ[i]≡0

cutpoint : {Γ Δ Θ Γⱼ : Ctx idxs} {m n l : Carrier idx ²}
       → Γ ≔ Δ ⊎ Θ
       → Γⱼ ≔ m at j ⊠ Γ
       → m ≔ n ∙² l
       → Σ[ Θⱼ ∈ Ctx idxs ] (Θⱼ ≔ l at j ⊠ Θ)
cutpoint (_ , γ≔) (zero x) m≔ =
  let
    _ , _ , a = ∙²-assoc x m≔
    _ , _ , c = ∙²-assoc (∙²-comm a) γ≔
  in _ , zero (∙²-comm c)
cutpoint (Γ≔ , _) (suc ∋j) m≔ with cutpoint Γ≔ ∋j m≔
cutpoint (Γ≔ , _) (suc ∋j) m≔ | _ , r = _ , suc r

midpoint : {Γᵢ Γ Δ Ψ ΔP Ξᵢ ΔQ Ψᵢ : Ctx idxs} {m n : Carrier idx ²}
         → Γᵢ ≔ m at i ⊠ Γ
         → Γ ≔ Δ ⊎ Ψ
         → All.lookup i Δ ≡ ℓ∅
         → Γᵢ ≔ ΔP ⊎ Ξᵢ
         → Ξᵢ ≔ ΔQ ⊎ Ψᵢ
         → Ψᵢ ≔ n at i ⊠ Ψ
         → Σ[ δ ∈ Carrier idx ² ]
           Σ[ Θ ∈ Ctx idxs ]
           Σ[ Δ₁ ∈ Ctx idxs ]
           Σ[ Δ₂ ∈ Ctx idxs ] (
           Ξᵢ ≔ δ at i ⊠ Θ
         × Γ ≔ Δ₁ ⊎ Θ
         × Θ ≔ Δ₂ ⊎ Ψ
         × All.lookup i Δ₁ ≡ ℓ∅
         × All.lookup i Δ₂ ≡ ℓ∅)

midpoint {i = zero} (zero γᵢ≔m∙γ) (Γ≔Δ∙Ψ , γ≔δ∙ψ) refl (Γᵢ≔ΔP∙Ξᵢ , γᵢ≔δp∙ξᵢ) (Ξᵢ≔ΔQ∙Ψᵢ , ξᵢ≔δq∙ψᵢ) (zero ψᵢ≔n∙ψ) rewrite ∙²-unique γ≔δ∙ψ ∙²-idˡ =
  let _ , ξᵢ≔δ∙θ , _ = ∙²-assoc⁻¹ ξᵢ≔δq∙ψᵢ ψᵢ≔n∙ψ in
  _ , _ , (_ -, _) , _ , zero ξᵢ≔δ∙θ , (Γᵢ≔ΔP∙Ξᵢ , ∙²-idˡ) , (Ξᵢ≔ΔQ∙Ψᵢ , ∙²-idˡ) , refl , refl
midpoint {i = suc i} (suc Γᵢ≔m∙Γ) (Γ≔Δ∙Ψ , _) Δ[i]≡ℓ∅ (Γᵢ≔ΔP∙Ξᵢ , γᵢ≔δp∙ξᵢ) (Ξᵢ≔ΔQ∙Ψᵢ , ξᵢ≔δq∙ψᵢ) (suc ψᵢ≔n∙ψ) with midpoint Γᵢ≔m∙Γ Γ≔Δ∙Ψ Δ[i]≡ℓ∅ Γᵢ≔ΔP∙Ξᵢ Ξᵢ≔ΔQ∙Ψᵢ ψᵢ≔n∙ψ
midpoint {i = suc i} (suc Γᵢ≔m∙Γ) (Γ≔Δ∙Ψ , _) Δ[i]≡ℓ∅ (Γᵢ≔ΔP∙Ξᵢ , γᵢ≔δp∙ξᵢ) (Ξᵢ≔ΔQ∙Ψᵢ , ξᵢ≔δq∙ψᵢ) (suc ψᵢ≔n∙ψ) | _ , _ , _ , _ , Ξᵢ≔δ∙Θ , Γ≔Δ₁∙Θ , Θ≔Δ₂∙Ψ , Δ₁[i]≡ℓ∅ , Δ₂[i]≡ℓ∅ =
  _ , _ , (_ -, _) , _ , suc Ξᵢ≔δ∙Θ , (Γ≔Δ₁∙Θ , γᵢ≔δp∙ξᵢ) , (Θ≔Δ₂∙Ψ , ξᵢ≔δq∙ψᵢ) , Δ₁[i]≡ℓ∅ , Δ₂[i]≡ℓ∅


⊢-subst-ih : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Γᵢ Γⱼ Δ Ψ Ψᵢ Ψⱼ : Ctx idxs} {i j : Fin n} {m n : Carrier idx ²}
           → γ ∝ Γᵢ [ i ]≔ t ∝ m ⊠ Γ
           → γ ∝ Γⱼ [ j ]≔ t ∝ m ⊠ Γ
           → γ ∝ Ψᵢ [ i ]≔ t ∝ n ⊠ Ψ
           → γ ∝ Ψⱼ [ j ]≔ t ∝ n ⊠ Ψ
           → Γ ≔ Δ ⊎ Ψ
           → All.lookup i Δ ≡ ℓ∅
           → γ ∝ Γᵢ ⊢ P ⊠ Ψᵢ
           → γ ∝ Γⱼ ⊢ [ j / i ] P ⊠ Ψⱼ

⊢-subst-ih {i = i} ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ end with ⊎-get i Γ≔Δ∙Ψ | ∋-≡Idx ∈i | ∋-≡Idx ∋i
⊢-subst-ih {i = i} ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ end | Γi≔Δi∙Ψi | refl | refl with Only-lookup-≡ (∋-Only ∈i) | Only-lookup-≡ (∋-Only ∋i)
⊢-subst-ih {i = i} ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ end | Γi≔Δi∙Ψi | refl | refl | eq | qe rewrite Δ∋iℓ∅ | ∙²-unique Γi≔Δi∙Ψi ∙²-idˡ | ∙²-uniqueˡ qe eq = {!eq!}

⊢-subst-ih ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (chan t m μ ⊢P) =
  chan t m μ (⊢-subst-ih (suc ∋i) (suc ∋j) (suc ∈i) (suc ∈j) (Γ≔Δ∙Ψ , ∙²-idʳ) Δ∋iℓ∅ ⊢P)

⊢-subst-ih {i = i} ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (recv {i = x} ∋x ⊢P) with ⊢-⊎ ⊢P | Only-⊎ (∋-Only ∋x) | i Finₚ.≟ x
⊢-subst-ih ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (recv ∋x ⊢P) | (_ -, _) , (Ξᵢ≔δ⊢P∙Ψᵢ , _) | _ , Γᵢ≔ℓ∙Ξᵢ , ℓ≔ℓ | yes refl with ∋-≡Idx ∋i | ∋-≡Idx ∋x
⊢-subst-ih ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (recv ∋x ⊢P) | (_ -, _) , (Ξᵢ≔δ⊢P∙Ψᵢ , _) | _ , Γᵢ≔ℓ∙Ξᵢ , ℓ≔ℓ | yes refl | refl | refl =
  let
    typecheck = trans (∋-≡Type ∋j) (trans (sym (∋-≡Type ∋i)) (∋-≡Type ∋x))
    δ , _ , _ , _ , Ξᵢ≔δ∙Θ , Γ≔Δ₁∙Θ , Θ≔Δ₂∙Ψ , Δ₁[i]≡0 , Δ₂[i]≡0 = midpoint (∋-Only ∋i) Γ≔Δ∙Ψ Δ∋iℓ∅ Γᵢ≔ℓ∙Ξᵢ Ξᵢ≔δ⊢P∙Ψᵢ (∋-Only ∈i)
    m≔ℓ∙δ = diff' (∋-Only ∋x) Ξᵢ≔δ∙Θ (∋-Only ∋i) Γ≔Δ₁∙Θ Δ₁[i]≡0
    Γᵢ' , Γᵢ≔ℓ∙Γᵢ' , Γᵢ'≔δ∙Γ = split m≔ℓ∙δ (∋-Only ∋i)
    Γⱼ' , Γⱼ≔ℓ∙Γⱼ' , Γⱼ'≔δ∙Γ = split m≔ℓ∙δ (∋-Only ∋j)
    Γᵢ'≡Ξᵢ = Only-uniqueʳ Γᵢ≔ℓ∙Γᵢ' (∋-Only ∋x)
    Ξᵢ≔δ∙Γ = subst (λ ● → ● ≔ _ at _ ⊠ _) Γᵢ'≡Ξᵢ Γᵢ'≔δ∙Γ
    Γ≡Θ = Only-uniqueʳ Ξᵢ≔δ∙Γ Ξᵢ≔δ∙Θ
    Ξⱼ≔δ∙Θ = subst (λ ● → Γⱼ' ≔ δ at _ ⊠ ●) Γ≡Θ Γⱼ'≔δ∙Γ
    ∋i' = Only-∋ Ξᵢ≔δ∙Θ (∋-≡Type ∋i)
    ∋j' = Only-∋ Ξⱼ≔δ∙Θ (∋-≡Type ∋j)
  in recv (Only-∋ Γⱼ≔ℓ∙Γⱼ' typecheck) (⊢-subst-ih (suc ∋i') (suc ∋j') (suc ∈i) (suc ∈j) (Θ≔Δ₂∙Ψ , ∙²-idʳ) Δ₂[i]≡0 ⊢P)

⊢-subst-ih ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (recv ∋x ⊢P) | (_ -, _) , (Ξᵢ≔δ⊢P∙Ψᵢ , _) | _ , Γᵢ≔ℓ⊠Ξᵢ , ℓ≔ℓ | no i≢x =
  let
    _ , _ , _ , _ , a , b , c , d , e = midpoint (∋-Only ∋i) Γ≔Δ∙Ψ Δ∋iℓ∅ Γᵢ≔ℓ⊠Ξᵢ Ξᵢ≔δ⊢P∙Ψᵢ (∋-Only ∈i)
    _ , f = cutpoint b (∋-Only ∋j) {!!}
    foo = Only-∋ a (∋-≡Type ∋i)
    bar = Only-∋ f (∋-≡Type ∋j)
  in recv (Only-∋ {!∋x!} {!!}) (⊢-subst-ih (suc foo) (suc bar) (suc ∈i) (suc ∈j) (c , ∙²-idʳ) e ⊢P)

⊢-subst-ih ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (send x y ⊢P) = {!!}
⊢-subst-ih ∋i ∋j ∈i ∈j Γ≔Δ∙Ψ Δ∋iℓ∅ (comp {Δ = Ξᵢ} ⊢P ⊢Q) =
  let
    _ , Γᵢ≔δ⊢P∙Ξᵢ = ⊢-⊎ ⊢P
    _ , Ξᵢ≔δ⊢Q∙Ψᵢ = ⊢-⊎ ⊢Q

    _ , _ , _ , _ , Ξᵢ≔δ∙Θ , Γ≔Δ₁∙Θ , Θ≔Δ₂∙Ψ , Δ₁[i]≡0 , Δ₂[i]≡0 = midpoint (∋-Only ∋i) Γ≔Δ∙Ψ Δ∋iℓ∅ Γᵢ≔δ⊢P∙Ξᵢ Ξᵢ≔δ⊢Q∙Ψᵢ (∋-Only ∈i)
    _ , m≔δ⊢p∙δ , _ = diff Γᵢ≔δ⊢P∙Ξᵢ Ξᵢ≔δ∙Θ (∋-Only ∋i) Γ≔Δ₁∙Θ Δ₁[i]≡0
    _ , Ξⱼ≔δ∙Θ = cutpoint Γ≔Δ₁∙Θ (∋-Only ∋j) m≔δ⊢p∙δ

    ∋i' = Only-∋ Ξᵢ≔δ∙Θ (∋-≡Type ∋i)
    ∋j' = Only-∋ Ξⱼ≔δ∙Θ (∋-≡Type ∋j)

  in comp (⊢-subst-ih ∋i ∋j ∋i' ∋j' Γ≔Δ₁∙Θ Δ₁[i]≡0 ⊢P) (⊢-subst-ih ∋i' ∋j' ∈i ∈j Θ≔Δ₂∙Ψ Δ₂[i]≡0 ⊢Q)


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
  ⊢P'' = ⊢-subst-ih (Only-∋ (zero ∙²-idʳ) refl) (suc y') (Only-∋ (zero ∙²-idʳ) refl) (Only-∋ (suc (Only-ℓ∅ (∋-≡Idx y))) (∋-≡Type y')) (⊢P'≔ , ∙²-idʳ) refl ⊢P'
  Γ≔ : ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
  Γ≔ with ⊢-⊎ ⊢P''
  Γ≔ | (_ -, _) , (x , _) = _ , x
