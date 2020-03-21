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

private
  variable
    n : ℕ
    i j : Fin n
    t : Type
    γ : PreCtx n
    idx : I
    idxs : Vec I n
    m l δ : Cs idx
    Γ Δ Δ' Ξ' Θ Ψ Ξ Ψ' Θ' Δₗ Δᵣ : Ctx idxs
    P : Scoped n



data _w_⊠_[_/_]_ : PreCtx n → {idxs : Vec I n} → Ctx idxs → Ctx idxs → Fin n → Fin n → Ctx idxs → Set where
  zero : m ≔ δ ∙ l
       → Γ ≔ Δ ⊎ Ψ
       → (j : γ w Ψ ∋ t w δ ⊠ Ξ)
       → γ -, t w Γ -, m ⊠ Ψ -, l [ suc (toFin j) / zero ] Ξ -, m

  suc : m ≔ δ ∙ l
      → γ w Γ ⊠ Ψ [ j / i ] Ξ
      → γ -, t w Γ -, m ⊠ Ψ -, l [ suc j / suc i ] Ξ -, l

subst-eq : γ w Γ ⊠ Γ [ j / i ] Ξ → Γ ≡ Ξ
subst-eq (zero x y j) rewrite ∙-uniqueˡ x (∙-idˡ _) | ∋-0∙ j = refl
subst-eq (suc _ x) rewrite subst-eq x = refl

split : Γ ≔ Δₗ ⊎ Δ
      → Δ ≔ Δᵣ ⊎ Ψ
      → γ w Γ ⊠ Ψ [ j / i ] Ξ
      → γ w Γ ⊠ Δ [ j / i ] Θ × γ w Δ ⊠ Ψ [ j / i ] Ξ
split {Δₗ = _ -, _} {Δ = _ -, _} {Δᵣ = _ -, _} {Θ = _ -, _} (a , b) (c , d) (zero x y j) = {!_w_⊠_[_/_]_.zero ? ? j!} , {!zero ? ? ?!}
split {Δₗ = _ -, _} {Δ = _ -, _} {Δᵣ = _ -, _} {Θ = _ -, _} (a , b) (c , d) (suc x e) with split a c e
split {Δₗ = _ -, _} {Δ = _ -, _} {Δᵣ = _ -, _} {Θ = _ -, _} (a , b) (c , d) (suc x e) | l , r = {!suc ? ?!} , (suc d r)

∋-subst : (x : γ w Γ ∋ t w m ⊠ Ξ)
    → γ w Γ ⊠ Ξ [ j / i ] Ψ
    → Σ[ y ∈ γ w Γ ∋ t w m ⊠ Ψ ]
      substFin j i (toFin x) ≡ toFin y
∋-subst (zero {check = check}) (zero x y j) rewrite ⊎-uniqueˡ y (⊎-idˡ _) | ∙-uniqueˡ x (proj₂ (toWitness check)) = suc j , refl
∋-subst (zero {check = check}) (suc _ s) rewrite subst-eq s = zero , refl
∋-subst (suc x) (zero y _ j) rewrite ∙-uniqueˡ y (∙-idˡ _) | ∋-0∙ j  = (suc x) , refl
∋-subst (suc x) (suc a s) with ∋-subst x s
∋-subst {i = suc i} (suc x) (suc a s) | y , eq with i Finₚ.≟ toFin x
∋-subst {i = suc i} (suc x) (suc a s) | y , eq | yes p = (suc y) , (cong suc eq)
∋-subst {i = suc i} (suc x) (suc a s) | y , eq | no ¬p = (suc y) , (cong suc eq)

foo : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ Ψ : Ctx idxs}
    → {i j : Fin n}
    → γ w Γ ⊢ P ⊠ Ψ
    → γ w Γ ⊠ Ψ [ j / i ] Ξ
    → γ w Γ ⊢ [ j / i ] P ⊠ Ξ
foo end xy rewrite subst-eq xy = end
foo (chan t m μ ⊢P) xy with ⊢-⊎ ⊢P
foo (chan t m μ ⊢P) xy | (_ -, _) , _ , b = chan t m μ (foo ⊢P (suc b xy) )
foo (recv x ⊢P) xy with ⊢-⊎ ⊢P
foo (recv x ⊢P) xy | (_ -, _) , a , b with split (∋-⊎ x) a xy
foo (recv x ⊢P) xy | (_ -, _) , a , b | l , r rewrite proj₂ (∋-subst x l) = recv _ (foo ⊢P (suc (∙-idʳ _) r))
foo (send x y ⊢P) xy = {!foo ⊢P !}
foo (comp ⊢P ⊢Q) xy with split (proj₂ (⊢-⊎ ⊢P)) (proj₂ (⊢-⊎ ⊢Q)) xy
foo (comp ⊢P ⊢Q) xy | l , r = comp (foo ⊢P l) (foo ⊢Q r)

⊢-subst' : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Cs idx}
         → γ -, t w Γ -, m ⊢ P ⊠ Ψ -, 0∙
         → (y : γ w Ψ ∋ t w m ⊠ Ξ)
         → γ -, t w Γ -, m ⊢ [ suc (toFin y) / zero ] P ⊠ Ξ -, m
⊢-subst' ⊢P y with ⊢-⊎ ⊢P
⊢-subst' ⊢P y | (_ -, _) , (Γ≔ , _) = foo ⊢P (zero (∙-idʳ _) Γ≔ y)

{- ∋-SUBSTGET -}
⊢-subst : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ Ψ : Ctx idxs} {t t'} {idx idx'}  {m : Cs idx} {m' : Cs idx'}
        → γ -, t' w Γ -, m' ⊢ P ⊠ Ψ -, 0∙
        → (y : γ w Ψ ∋ t w m ⊠ Ξ)
        → γ -, t' w Γ -, m' ⊢ [ suc (toFin y) / zero ] P ⊠ Ξ -, m'
