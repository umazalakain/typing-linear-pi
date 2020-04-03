open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
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

data _∝_[_/_]≔_∝_⊠[_/_] : PreCtx n → Ctx idxs → Fin n → Fin n → Type → Carrier idx ² → Ctx idxs → Ctx idxs → Set where
  zero : {Γ Ψ Ξ : Ctx idxs}
       → m ≔ δ ∙² l
       → γ ∝ Γ [ j ]≔ t ∝ δ ⊠ Ξ
       → γ -, t ∝ Γ -, m [ suc j / zero ]≔ t ∝ δ ⊠[ Ξ -, m / Ψ -, l ]

  suc : γ      ∝ Γ      [ j     / i     ]≔ t ∝ δ ⊠[ Ξ      / Ψ      ]
      → γ -, t ∝ Γ -, m [ suc j / suc i ]≔ t ∝ δ ⊠[ Ξ -, m / Ψ -, m ]

extract-left : γ ∝ Γ [ j / i ]≔ t ∝ δ ⊠[ Ξ / Ψ ]
             → γ ∝ Γ [ j     ]≔ t ∝ δ ⊠ Ξ
extract-left (zero _ x) = suc x
extract-left (suc sp) = suc (extract-left sp)

extract-right : γ ∝ Γ [ j / i ]≔ t ∝ δ ⊠[ Ξ / Ψ ]
              → γ ∝ Γ [ i     ]≔ t ∝ δ ⊠ Ψ
extract-right (zero x _) = {!zero ⦃ ? ⦄!}
extract-right (suc sp) = suc (extract-right sp)

feedback : {Γ M N : Ctx idxs}
         → m ≔ δ ∙² l
         → γ ∝ N [ i ]≔ t ∝ δ ⊠ M
         → γ ∝ Γ [ i ]≔ t ∝ m ⊠ M
         → γ ∝ Γ [ i ]≔ t ∝ l ⊠ N
feedback m (zero ⦃ a ⦄) (zero ⦃ b ⦄) = {!zero!}
feedback m (suc N) (suc Γ) = suc (feedback m N Γ)

∋-subst : {Γ Δ Ψₗ' Ψᵣ Ψₗ Ξ Ξ' : Ctx idxs}
        → Γ ≔ Δ ⊎ Ψₗ'
        → m ≔ δ ∙² l
        → γ ∝ Ψᵣ  [ j ]≔ t ∝ δ ⊠ Ξ'
        → γ ∝ Ψₗ' [ j ]≔ t ∝ m ⊠ Ψᵣ
        → γ ∝ Γ   [ i ]≔ t ∝ l ⊠ Ξ
        → γ ∝ Γ   [ j ]≔ t ∝ l ⊠ Ξ'

∙-≤ : γ ∝ Γ [ i ]≔ t ∝ l ⊠ Ξ
    → γ ∝ Γ [ i ]≔ t ∝ m ⊠ Ψ
    → All.lookup i Ξ ≡ (0∙ , 0∙)
    → ∃[ δ ] (m ≔ δ ∙² l)

foo : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Δ Ψₗ' Ψₗ Ψᵣ : Ctx idxs} {i j : Fin n} {m : Carrier idx ²}
    → γ ∝ Ψₗ' [ j / i ]≔ t ∝ m ⊠[ Ψᵣ / Ψₗ ]
    → All.lookup i Ψₗ ≡ (0∙ , 0∙)
    → Γ ≔ Δ ⊎ Ψₗ'
    → γ ∝ Γ ⊢ P ⊠ Ψₗ
    → γ ∝ Γ ⊢ [ j / i ] P ⊠ Ψᵣ
foo sp eq Γ≔ end = {!!}
foo sp eq Γ≔ (chan t m μ ⊢P) = chan t m μ (foo (suc {!sp!}) eq (Γ≔ , ∙²-idʳ _) ⊢P)
foo {i = i} sp eq Γ≔ (recv {i = i'} x ⊢P) with i Finₚ.≟ i'
foo {i = i} sp eq Γ≔ (recv {i = .i} x ⊢P) | yes refl = recv ? ?
foo {i = i} sp eq Γ≔ (recv {i = i'} x ⊢P) | no ¬p = recv x (foo (suc {!!}) eq ({!!} , ∙²-idʳ _) ⊢P)
foo sp eq Γ≔ (send x y ⊢P) = {!!}
foo sp eq Γ≔ (comp ⊢P ⊢P₁) = {!!}

⊢-subst' : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Carrier idx ²}
         → γ -, t ∝ Γ -, m ⊢ P ⊠ Ψ -, ℓ∅
         → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
         → γ -, t ∝ Γ -, m ⊢ [ suc j / zero ] P ⊠ Ξ -, m
⊢-subst' ⊢P y with ⊢-⊎ ⊢P
⊢-subst' ⊢P y | (pctx -, rctx) , (p≔ , r≔) = foo (zero (∙²-idʳ _) y) refl (p≔ , ∙²-idˡ _) ⊢P

postulate
  {- TARGET -}
  ⊢-subst : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t t'} {idx idx'}  {m : Carrier idx ²} {m' : Carrier idx' ²}
          → γ -, t' ∝ Γ -, m' ⊢ P ⊠ Ψ -, (0∙ , 0∙)
          → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
          → γ -, t' ∝ Γ -, m' ⊢ [ suc j / zero ] P ⊠ Ξ -, m'
