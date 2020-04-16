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
    Γ Δ Δ' Ξ' Θ Ψ Ξ Ψ' Θ' Δₗ Δᵣ : Ctx idxs
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

foo : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Δ Ψₘ Ψₗ Ψᵣ : Ctx idxs} {i j : Fin n} {m : Carrier idx ²}
    → Ψₘ ≔ m at i ⊠ Ψₗ
    → Ψₘ ≔ m at j ⊠ Ψᵣ
    → i Fin.≤ j
    → All.lookup i Δ ≡ ℓ∅
    → Γ ≔ Δ ⊎ Ψₘ
    → γ ∝ Γ ⊢ P ⊠ Ψₗ
    → γ ∝ Γ ⊢ [ j / i ] P ⊠ Ψᵣ

foo ∋i ∋j i≤j eq Γ≔ end with Only-⊎ ∋i | Only-⊎ ∋j
foo ∋i ∋j i≤j eq Γ≔ end | _ , Ψₘ≔m∙Γ , _ | _ , Ψₘ≔m∙Ψᵣ , _
  rewrite ⊎-mut-cancel Γ≔ Ψₘ≔m∙Γ | ε-Only ∋i | Only-ε ∋j = end

foo ∋i ∋j i≤j eq Γ≔ (chan t m μ ⊢P)
  = chan t m μ (foo (suc ∋i) (suc ∋j) (Nat.s≤s i≤j) eq (Γ≔ , ∙²-idʳ) ⊢P)

foo {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = x} ∋x ⊢P) with i Finₚ.≟ x | Only-⊎ (∋-Only ∋x) | Only-⊎ ∋i | Only-⊎ ∋j | ⊢-⊎ ⊢P
foo {Ψₘ = Ψₘ} {i = i} {m = m} ∋i ∋j i≤j eq Γ≔ (recv {i = x} ∋x ⊢P) | yes refl | _ , Γ≔ℓᵢatx∙Ξₗ , ℓᵢatx≔ℓᵢatx | mati , Ψₘ≔m∙Ψₗ , _ | matj , Ψᵣ≔m∙Ψₗ , _ | (_ -, _) , (⊢P≔ , _)
  = let m' , Γ≔m'∙Ψₗ , m'≔ℓᵢ∙⊢P = ∙²-assoc⁻¹ (⊎-get i Γ≔ℓᵢatx∙Ξₗ) (⊎-get i ⊢P≔)
        m'≔ℓᵢ∙⊢P = hsubst (λ ● → ● ≔ _ ∙² _) {!!} {!!} -- (lookup-only i {m} (∋-≡Idx ∋i))
     in
  recv (∋-frame {!∋i!} {!!} {!!}) {!!}
{-
foo {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = i'} x ⊢P) with ∋-I ∋i | ∋-I x | i Finₚ.≟ i' | ⊢-⊎ ⊢P
foo {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = .i} x ⊢P) | refl | refl | yes refl | (Ξₗ -, _) , (Ξₗ≔ , _) with ∙²-assoc⁻¹ (⊎-get i (∋-⊎ x)) (⊎-get i Ξₗ≔)
foo {idxs = idxs} {i = i} {m = m} ∋i ∋j i≤j eq Γ≔ (recv {i = .i} x ⊢P) | refl | refl | yes refl | (Ξₗ -, _) , (Ξₗ≔ , _) | δ , Γ≔δ∙Ψₗ , δ≔ℓᵢ∙⊢P
  rewrite ∋-t ∋i | sym (∋-t x)
  | ∙²-unique (⊎-get i Γ≔) (subst (λ ● → _ ≔ ● ∙² _) (sym eq) ∙²-idˡ)
  | ∙²-uniqueˡ Γ≔δ∙Ψₗ (⊎-get i (∋-⊎ ∋i))
  =
  let m≔ℓᵢ∙δ = hsubst (λ ● → ● ≔ _ ∙² _)
                      (lookup-only i {m} (∋-I ∋i))
                      (hsubst (λ ● → _ ≔ ● ∙² _)
                              (lookup-only i {ℓᵢ} (∋-I x))
                              δ≔ℓᵢ∙⊢P)
      ξ , Ψₘ≔ℓᵢ⊎ξ , ξ≔Ξₗᵢ⊎Ψₗ = ⊎-assoc (∋-⊎ ∋i) (only-∙ i (∋-I ∋i) m≔ℓᵢ∙δ)
      Ψₘ≔ℓᵢ⊎ξ' = subst (λ ● → _ ≔ ● ⊎ ξ) (only-irrel (∋-I ∋i) (∋-I x)) Ψₘ≔ℓᵢ⊎ξ
  in recv
     (∋-frame Ψₘ≔ℓᵢ⊎ξ' (∋-⊎ x) (∋-feedback m≔ℓᵢ∙δ {!Γ≔δ∙Ψₗ!} ∋j))
     {!!}



foo {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = i'} x ⊢P) | refl | refl | no ¬p | (_ -, _) , (Ξₗ≔ , _) = recv x (foo (suc ∋i) (suc ∋j) (Nat.s≤s i≤j) eq ({!!} , ∙²-idʳ) ⊢P)
     -}

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

foo ∋i ∋j i≤j eq Γ≔ (send x y ⊢P) = {!!}

foo ∋i ∋j i≤j eq Γ≔ (comp ⊢P ⊢Q) = comp (foo {!!} {!!} i≤j {!eq!} {!!} ⊢P) {!!}

⊢-subst' : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Carrier idx ²}
         → γ -, t ∝ Γ -, m ⊢ P ⊠ Ψ -, ℓ∅
         → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
         → γ -, t ∝ Γ -, m ⊢ [ suc j / zero ] P ⊠ Ξ -, m
⊢-subst' ⊢P y with ⊢-⊎ ⊢P
⊢-subst' ⊢P y | (pctx -, rctx) , (p≔ , r≔) = foo (zero ∙²-idʳ) (suc (∋-Only y)) Nat.z≤n refl (p≔ , ∙²-idˡ) ⊢P

postulate
  {- TARGET -}
  ⊢-subst : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t t'} {idx idx'}  {m : Carrier idx ²} {m' : Carrier idx' ²}
          → γ -, t' ∝ Γ -, m' ⊢ P ⊠ Ψ -, ℓ∅
          → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
          → γ -, t' ∝ Γ -, m' ⊢ [ suc j / zero ] P ⊠ Ξ -, m'
 
