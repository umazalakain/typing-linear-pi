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
    Γ Γₗ Γᵣ Ξₗ Ξᵣ Δ Δ' Ξ' Θ Ψ Ξ Ψ' Θ' Δₗ Δᵣ : Ctx idxs
    P : Scoped n

{-
≡-Only-⊎ : {idxs : Idxs n} {Γ xati : Ctx idxs}
          → (i : Fin n)
          → All.lookup i Γ ≡ All.lookup i xati
          → xati ≔ x at i ⊠ ε {idxs = idxs}
          → Σ[ Δ ∈ Ctx idxs ]
            (Γ ≔ Δ ⊎ xati × All.lookup i Δ ≡ ℓ∅)

≡-Only-⊎ {Γ = _ -, _} zero refl (zero x) = _ , (⊎-idʳ , ∙²-idˡ) , refl
≡-Only-⊎ {Γ = _ -, _} (suc i) eq (suc xati) with ≡-Only-⊎ i eq xati
≡-Only-⊎ {Γ = _ -, _} (suc i) eq (suc xati) | _ , Γ≔ , eq' = _ , (Γ≔ , ∙²-idʳ) , eq'

Only-frame : {Γₗ Γᵣ Ψₗ Ψᵣ Δ : Ctx idxs}
           → Γₗ ≔ Δ ⊎ Γᵣ
           → Ψₗ ≔ Δ ⊎ Ψᵣ
           → Γᵣ ≔ m at i ⊠ Ψᵣ
           → Γₗ ≔ m at i ⊠ Ψₗ
Only-frame Γ Ψ ∋i = {!!}

bar : {i j x : Fin n} {Ψₘ Ψₗ Ψᵣ Γ Δ Ξ : Ctx idxs}
    → Ψₘ ≔ m at i ⊠ Ψₗ
    → Ψₘ ≔ m at j ⊠ Ψᵣ
    → i Fin.≤ j
    → All.lookup i Δ ≡ ℓ∅
    → Γ ≔ Δ ⊎ Ψₘ
    → Γ ≔ m at x ⊠ Ξ
    → Ξ ≔ Θ ⊎ Ψₗ
    → Σ[ W ∈ Ctx idxs ] Γ ≔ m at substFin j i x ⊠ W
bar {i = i} {j} {x} ∋i ∋j i≤j Δi Γ≔ ∋x Ξ≔ with i Finₚ.≟ x
bar {i = i} {j} {.i} (zero ∋i) (zero ∋j) i≤j Δi Γ≔ (zero ∋x) Ξ≔ | yes refl = _ , zero ∋x
bar {i = i} {suc j} {.i} (zero ∋i) (suc ∋j) i≤j refl (Γ≔ , _) (zero ∋x) (Ξ≔ , _) | yes refl = {!!} , suc (Only-frame Γ≔ {!∋x!} {!!})
bar {i = suc i} {suc j} {suc .i} (suc ∋i) (suc ∋j) (Nat.s≤s i≤j) Δi (Γ≔ , _) (suc ∋x) (Ξ≔ , _) | yes refl with bar ∋i ∋j i≤j Δi Γ≔ ∋x Ξ≔
bar {i = suc i} {suc j} {suc .i} (suc ∋i) (suc ∋j) i≤j Δi Γ≔ (suc ∋x) Ξ≔ | yes refl | _ , ∋x' with i Finₚ.≟ i
bar {i = suc i} {suc j} {suc .i} (suc ∋i) (suc ∋j) i≤j Δi Γ≔ (suc ∋x) Ξ≔ | yes refl | _ , ∋x' | yes refl = _ , suc ∋x'
bar {i = suc i} {suc j} {suc .i} (suc ∋i) (suc ∋j) i≤j Δi Γ≔ (suc ∋x) Ξ≔ | yes refl | _ , ∋x' | no ¬p = ⊥-elim (¬p refl)
bar {i = i} {j} {x} ∋i ∋j i≤j Δi Γ≔ ∋x Ξ≔ | no ¬p = _ , ∋x

foo : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Δ Ψₘ Ψₗ Ψᵣ : Ctx idxs} {i j : Fin n} {m : Carrier idx ²}
    → γ ∝ Ψₘ [ i ]≔ t ∝ m ⊠ Ψₗ
    → γ ∝ Ψₘ [ j ]≔ t ∝ m ⊠ Ψᵣ
    → i Fin.≤ j
    → All.lookup i Δ ≡ ℓ∅
    → Γ ≔ Δ ⊎ Ψₘ
    → γ ∝ Γ ⊢ P ⊠ Ψₗ
    → γ ∝ Γ ⊢ [ j / i ] P ⊠ Ψᵣ

foo ∋i ∋j i≤j eq Γ≔ end with ∋-⊎ ∋i
foo ∋i ∋j i≤j eq Γ≔ end | _ , Ψₘ≔m∙Γ
  rewrite ⊎-mut-cancel Γ≔ Ψₘ≔m∙Γ | Only-≡ℓ∅ (∋-Only ∋i) | Only-ℓ∅-≡ (∋-Only ∋j) = end

foo ∋i ∋j i≤j eq Γ≔ (chan t m μ ⊢P)
  = chan t m μ (foo (suc ∋i) (suc ∋j) (Nat.s≤s i≤j) eq (Γ≔ , ∙²-idʳ) ⊢P)

foo {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = x} ∋x ⊢P) with ∋-Only ∋i | ∋-Only ∋j | ∋-Only ∋x | ⊢-⊎ ⊢P
foo {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = x} ∋x ⊢P) | O∋i | O∋j | O∋x | (_ -, _) , (Ξ≔ , _) = {!!}
{-
foo {idxs = idxs} {Ψₘ = Ψₘ} {i = i} {m = m} ∋i ∋j i≤j eq Γ≔ (recv {i = x} ∋x ⊢P) | yes refl | ℓᵢati , Γ≔ℓᵢati∙Ξₗ , ℓᵢati≔ℓᵢati | mati , Ψₘ≔m∙Ψₗ , mati≔mati | matj , Ψᵣ≔m∙Ψₗ , matj≔matj | (_ -, _) , (⊢P≔ , _)
  = let γⱼ≡C[] = trans (sym (∋-≡Type ∋j)) (trans (∋-≡Type ∋i) (sym (∋-≡Type ∋x)))

        ℓᵢati∙⊢Pᵢ , Γᵢ≔[ℓᵢati∙⊢Pᵢ]∙Ψₗ , ℓᵢati∙⊢Pᵢ≔ℓᵢati∙⊢Pᵢ = ∙²-assoc⁻¹ (⊎-get i Γ≔ℓᵢati∙Ξₗ) (⊎-get i ⊢P≔)

        Δᵢ∙m , Γᵢ≔[Δᵢ∙m]∙Ψₗ , Δᵢ∙m≔Δᵢ∙m = ∙²-assoc⁻¹ (⊎-get i Γ≔) (⊎-get i Ψₘ≔m∙Ψₗ)
        Δᵢ∙m≡m = ∙²-unique (subst (λ ● → Δᵢ∙m ≔ ● ∙² _) eq Δᵢ∙m≔Δᵢ∙m) ∙²-idˡ
        Γᵢ≔m∙Ψₗ = subst (λ ● → _ ≔ ● ∙² _) Δᵢ∙m≡m Γᵢ≔[Δᵢ∙m]∙Ψₗ

        ℓᵢati∙⊢Pᵢ≡m = ∙²-uniqueˡ Γᵢ≔[ℓᵢati∙⊢Pᵢ]∙Ψₗ  Γᵢ≔m∙Ψₗ
        m≔ℓᵢ∙⊢P = subst (λ ● → ● ≔ _ ∙² _) ℓᵢati∙⊢Pᵢ≡m ℓᵢati∙⊢Pᵢ≔ℓᵢati∙⊢Pᵢ
     in
  recv
    (∋-frame
    (proj₁ (proj₂ (Only-⊎ (proj₂ blabla)))) -- From where: Ψₘ ≔ ℓᵢ at j ⊠ ?1
    {!!} -- To where: Γ ≔ ℓ₁ at j ⊠ ?2
    (Only-∋ (proj₂ blabla) γⱼ≡C[]))
    (⊢-frame {!∋x!} {!!} (foo (suc ∋i) (suc ∋j) {!!} {!!} {!!} ⊢P)) -- ?2 ≔ ⊢P [j/i] ⊎ ?1

  where
  blabla : Σ[ ⁇ ∈ Ctx idxs ] (Ψₘ ≔ ℓᵢ at j ⊠ ⁇)

foo {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = x} ∋x ⊢P) | no i≢x    | _ , Γ≔ℓᵢatx∙Ξₗ , ℓᵢatx≔ℓᵢatx | mati , Ψₘ≔m∙Ψₗ , mati≔mati | matj , Ψᵣ≔m∙Ψₗ , _ | (_ -, _) , (⊢P≔ , _)
  = let Δᵢ∙m , Γᵢ≔[Δᵢ∙m]∙Ψₗ , Δᵢ∙m≔Δᵢ∙m = ∙²-assoc⁻¹ (⊎-get i Γ≔) (⊎-get i Ψₘ≔m∙Ψₗ)
        Δᵢ∙m≡m = ∙²-unique (subst (λ ● → Δᵢ∙m ≔ ● ∙² _) eq Δᵢ∙m≔Δᵢ∙m) ∙²-idˡ
        Γᵢ≔m∙Ψₗ = subst (λ ● → _ ≔ ● ∙² _) Δᵢ∙m≡m Γᵢ≔[Δᵢ∙m]∙Ψₗ

        ℓᵢatx∙⊢Pᵢ , Γᵢ≔[ℓᵢatx∙⊢Pᵢ]∙Ψₗ , ℓᵢatx∙⊢Pᵢ≔ℓᵢatx∙⊢Pᵢ = ∙²-assoc⁻¹ (⊎-get i Γ≔ℓᵢatx∙Ξₗ) (⊎-get i ⊢P≔)
        ℓᵢatxati≡ℓ∅ = trans (Only-lookup-≢ ℓᵢatx≔ℓᵢatx i (i≢x ∘ sym)) (lookup-ε i)
        ℓᵢatx∙⊢Pᵢ≡⊢Pᵢ = ∙²-unique (subst (λ ● → ℓᵢatx∙⊢Pᵢ ≔ ● ∙² _) ℓᵢatxati≡ℓ∅ ℓᵢatx∙⊢Pᵢ≔ℓᵢatx∙⊢Pᵢ) ∙²-idˡ
        Γᵢ≔⊢Pᵢ∙Ψₗ = subst (λ ● → _ ≔ ● ∙² _) ℓᵢatx∙⊢Pᵢ≡⊢Pᵢ Γᵢ≔[ℓᵢatx∙⊢Pᵢ]∙Ψₗ

        ⊢Pᵢ≡m = ∙²-uniqueˡ Γᵢ≔⊢Pᵢ∙Ψₗ Γᵢ≔m∙Ψₗ
        ⁇ , ⊢P≔⁇⊎mati , ⁇ᵢ≡ℓ∅ = ≡-Only-⊎ i ⊢Pᵢ≡m mati≔mati
  in recv ∋x (foo (suc ∋i) (suc ∋j) (Nat.s≤s i≤j) ⁇ᵢ≡ℓ∅ (feedback ⊢P≔⁇⊎mati Ψₘ≔m∙Ψₗ ⊢P≔ , ∙²-idʳ) ⊢P)
  -}

foo ∋i ∋j i≤j eq Γ≔ (send x y ⊢P) = {!!}

foo ∋i ∋j i≤j eq Γ≔ (comp ⊢P ⊢Q) = comp (foo {!!} {!!} i≤j {!eq!} {!!} ⊢P) 

⊢-subst' : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Carrier idx ²}
         → γ -, t ∝ Γ -, m ⊢ P ⊠ Ψ -, ℓ∅
         → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
         → γ -, t ∝ Γ -, m ⊢ [ suc j / zero ] P ⊠ Ξ -, m
⊢-subst' ⊢P y with ⊢-⊎ ⊢P
⊢-subst' ⊢P y | (pctx -, rctx) , (p≔ , r≔) = foo (Only-∋ (zero ∙²-idʳ) refl) (suc y) Nat.z≤n refl (p≔ , ∙²-idˡ) ⊢P
-}

postulate
  {- TARGET -}
  ⊢-subst : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t t'} {idx idx'}  {m : Carrier idx ²} {m' : Carrier idx' ²}
          → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
          → γ -, t' ∝ Γ -, m' ⊢ P ⊠ Ψ -, ℓ∅
          → γ -, t' ∝ Γ -, m' ⊢ [ suc j / zero ] P ⊠ Ξ -, m'
 
