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
    m m' l δ : Carrier idx ²
    Γ Δ Δ' Ξ' Θ Ψ Ξ Ψ' Θ' Δₗ Δᵣ : Ctx idxs
    P : Scoped n

feedback : {Γ M N : Ctx idxs}
         → m ≔ δ ∙² l
         → γ ∝ N [ i ]≔ t ∝ l ⊠ M
         → γ ∝ Γ [ i ]≔ t ∝ m ⊠ M
         → γ ∝ Γ [ i ]≔ t ∝ δ ⊠ N
feedback m≔δ∙l (zero ⦃ a ⦄) (zero ⦃ b ⦄) with toWitness a | toWitness b
feedback m≔δ∙l (zero ⦃ a ⦄) (zero ⦃ b ⦄) | w , w≔l∙z | v , v≔m∙z with ∙²-assoc v≔m∙z m≔δ∙l
feedback m≔δ∙l (zero ⦃ a ⦄) (zero ⦃ b ⦄) | w , w≔l∙z | v , v≔m∙z | w' , v≔δ∙w' , w'≔l∙z
  rewrite ∙²-unique w≔l∙z w'≔l∙z | ∙²-compute-unique v≔δ∙w' = zero ⦃ fromWitness (_ , v≔δ∙w') ⦄
feedback s (suc N) (suc Γ) = suc (feedback s N Γ)

foo : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Δ Ψₘ Ψₗ Ψᵣ : Ctx idxs} {i j : Fin n} {m : Carrier idx ²}
    → γ ∝ Ψₘ [ i ]≔ t ∝ m ⊠ Ψₗ
    → γ ∝ Ψₘ [ j ]≔ t ∝ m ⊠ Ψᵣ
    → i Fin.≤ j
    → All.lookup i Δ ≡ ℓ∅
    → Γ ≔ Δ ⊎ Ψₘ
    → γ ∝ Γ ⊢ P ⊠ Ψₗ
    → γ ∝ Γ ⊢ [ j / i ] P ⊠ Ψᵣ

foo ∋i ∋j i≤j eq Γ≔ end rewrite ⊎-mut-cancel Γ≔ (∋-⊎ ∋i) | 0∙-∋ ∋i (sym (⊎-mut-cancel Γ≔ (∋-⊎ ∋i))) | ∋-0∙ ∋j = end

foo ∋i ∋j i≤j eq Γ≔ (chan t m μ ⊢P) = chan t m μ (foo (suc ∋i) (suc ∋j) (Nat.s≤s i≤j) eq (Γ≔ , ∙²-idʳ) ⊢P)

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
     (∋-frame Ψₘ≔ℓᵢ⊎ξ' (∋-⊎ x) (feedback m≔ℓᵢ∙δ {!!} ∋j))
     {!!}



foo {i = i} ∋i ∋j i≤j eq Γ≔ (recv {i = i'} x ⊢P) | refl | refl | no ¬p | (_ -, _) , (Ξₗ≔ , _) = recv x (foo (suc ∋i) (suc ∋j) (Nat.s≤s i≤j) eq ({!!} , ∙²-idʳ) ⊢P)

foo ∋i ∋j i≤j eq Γ≔ (send x y ⊢P) = {!!}

foo ∋i ∋j i≤j eq Γ≔ (comp ⊢P ⊢Q) = comp (foo {!!} {!!} i≤j {!eq!} {!!} ⊢P) {!!}

⊢-subst' : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Carrier idx ²}
         → γ -, t ∝ Γ -, m ⊢ P ⊠ Ψ -, ℓ∅
         → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
         → γ -, t ∝ Γ -, m ⊢ [ suc j / zero ] P ⊠ Ξ -, m
⊢-subst' ⊢P y with ⊢-⊎ ⊢P
⊢-subst' ⊢P y | (pctx -, rctx) , (p≔ , r≔) = foo
  (subst (λ ● → _ ∝ _ -, ● [ _ ]≔ _ ∝ _ ⊠ _)
         (sym (∙²-compute-unique ∙²-idʳ))
         (zero ⦃ fromWitness (_ , ∙²-idʳ) ⦄))
  (suc y) Nat.z≤n refl (p≔ , ∙²-idˡ) ⊢P

postulate
  {- TARGET -}
  ⊢-subst : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t t'} {idx idx'}  {m : Carrier idx ²} {m' : Carrier idx' ²}
          → γ -, t' ∝ Γ -, m' ⊢ P ⊠ Ψ -, ℓ∅
          → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
          → γ -, t' ∝ Γ -, m' ⊢ [ suc j / zero ] P ⊠ Ξ -, m'
