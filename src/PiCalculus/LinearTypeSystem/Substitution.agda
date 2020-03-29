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
    m m' l δ : Carrier idx
    Γ Δ Δ' Ξ' Θ Ψ Ξ Ψ' Θ' Δₗ Δᵣ : Ctx idxs
    P : Scoped n


{-
data _∝_[_/_]_ : PreCtx n → {idxs : Vec I n} → Ctx idxs → Fin n → Fin n → Ctx idxs → Set where
  zero : m ≔ δ ∙ l
       → γ ∝ Ψ [ j ]≔ t ∝ δ ⊠ Ξ
       → γ -, t ∝ Ψ -, l [ suc j / zero ] Ξ -, m

  suc : γ ∝ Ψ [ j / i ] Ξ
      → γ -, t ∝ Ψ -, l [ suc j / suc i ] Ξ -, l

{-
subst-eq : γ ∝ Γ ⊠ Γ [ j / i ] Ξ → Γ ≡ Ξ
subst-eq (zero x y j) rewrite ∙-uniqueˡ x (∙-idˡ _) | ∋-ℓ∅ j = refl
subst-eq (suc _ x) rewrite subst-eq x = refl

split : Γ ≔ Δₗ ⊎ Δ
      → Δ ≔ Δᵣ ⊎ Ψ
      → γ ∝ Γ ⊠ Ψ [ j / i ] Ξ
      → γ ∝ Γ ⊠ Δ [ j / i ] Θ × γ ∝ Δ ⊠ Ψ [ j / i ] Ξ
split {Δₗ = _ -, _} {Δ = _ -, _} {Δᵣ = _ -, _} {Θ = _ -, _} (a , b) (c , d) (zero x y j) = {!_w_⊠_[_/_]_.zero ? ? j!} , {!zero ? ? ?!}
split {Δₗ = _ -, _} {Δ = _ -, _} {Δᵣ = _ -, _} {Θ = _ -, _} (a , b) (c , d) (suc x e) with split a c e
split {Δₗ = _ -, _} {Δ = _ -, _} {Δᵣ = _ -, _} {Θ = _ -, _} (a , b) (c , d) (suc x e) | l , r = {!suc ? ?!} , {!!}
-}

∋-subst : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ψₗ Ψᵣ Δ Δₗ Δᵣ : Ctx idxs} {i j : Fin n} {idx}
        → (eq : idx ≡ Vec.lookup idxs j)
        → Γ ≔ only j ℓᵢ ⊎ Ψᵣ
        → γ ∝ Γ [ j ]≔ t ∝ ℓᵢ {idx} ⊠ Ψᵣ
∋-subst {γ = _ -, _} {Γ = _ -, _} {Ψᵣ = _ -, _} {j = zero} refl (Γ≔ , r) = {!zero {check = fromWitness (_ , r)}!}
∋-subst {γ = _ -, _} {Γ = _ -, _} {Ψᵣ = _ -, _} {j = suc j} eq r = {!!}

foo : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ψₗ Ψᵣ Δ Δₗ Δᵣ : Ctx idxs} {i j : Fin n} {m : Cs (Vec.lookup idxs i)}
    → (eq : Vec.lookup idxs i ≡ Vec.lookup idxs j)
    → i Fin.≤ j
    → Δₗ ≔ only i m ⊎ Δ
    → Δᵣ ≔ only j (subst Cs eq m) ⊎ Δ
    → Γ ≔ Δₗ ⊎ Ψₗ
    → Γ ≔ Δᵣ ⊎ Ψᵣ
    → γ ∝ Γ ⊢ P ⊠ Ψₗ
    → γ ∝ Γ ⊢ [ j / i ] P ⊠ Ψᵣ
foo eq x≤y Δₗ Δᵣ Γₗ≔ Γᵣ≔ end rewrite ⊎-uniqueˡ Γₗ≔ (⊎-idˡ _) = {!!}
foo eq x≤y Δₗ Δᵣ Γₗ≔ Γᵣ≔ (chan t m μ ⊢P) = chan t m μ (foo eq (Nat.s≤s x≤y) (Δₗ , ∙-idˡ _) (Δᵣ , ∙-idˡ _) (Γₗ≔ , ∙-idʳ _) (Γᵣ≔ , ∙-idʳ _) ⊢P)
foo {i = i} {j = j} eq x≤y Δₗ Δᵣ Γₗ≔ Γᵣ≔ (recv x ⊢P) with ⊢-⊎ ⊢P | i Finₚ.≟ {!!}
foo {i = i} {j = j} eq x≤y Δₗ Δᵣ Γₗ≔ Γᵣ≔ (recv x ⊢P) | (_ -, _) , (P≔ , _) | yes p = recv {!!} {!!}
foo {i = i} {j = j} eq x≤y Δₗ Δᵣ Γₗ≔ Γᵣ≔ (recv x ⊢P) | (_ -, _) , (P≔ , _) | no ¬p = recv {!!} (foo eq (Nat.s≤s x≤y) ({!!} , ∙-idˡ _) ({!!} , ∙-idˡ _) ({!x!} , ∙-idʳ _) ({!!} , ∙-idʳ _) ⊢P)
foo eq x≤y Δₗ Δᵣ Γₗ≔ Γᵣ≔ (send x y ⊢P) = {!!}
foo eq x≤y Δₗ Δᵣ Γₗ≔ Γᵣ≔ (comp ⊢P ⊢Q) = comp (foo eq x≤y {!!} {!!} (proj₂ (⊢-⊎ ⊢P)) {!!} ⊢P) (foo eq x≤y {!!} {!!} (proj₂ (⊢-⊎ ⊢Q)) {!!} ⊢Q)

⊢-subst' : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ Ψ : Ctx idxs} {t  idx}  {m : Cs idx}
         → γ -, t ∝ Γ -, m ⊢ P ⊠ Ψ -, ℓ∅
         → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
         → γ -, t ∝ Γ -, m ⊢ [ suc j / zero ] P ⊠ Ξ -, m
⊢-subst' ⊢P y with ⊢-⊎ ⊢P
⊢-subst' ⊢P y | (_ -, _) , (Γ≔ , x≔) = foo (∋-I y) Nat.z≤n (⊎-idˡ _ , ∙-idʳ _) ({!!} , (∙-idˡ _)) (Γ≔ , ∙-idʳ _) (⊎-trans Γ≔ (∋-⊎ y) , ∙-idˡ _) ⊢P
-}

postulate
  {- TARGET -}
  ⊢-subst : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ Ψ : Ctx idxs} {t t'} {idx idx'}  {m : Carrier idx ²} {m' : Carrier idx' ²}
          → γ -, t' ∝ Γ -, m' ⊢ P ⊠ Ψ -, (0∙ , 0∙)
          → γ ∝ Ψ [ j ]≔ t ∝ m ⊠ Ξ
          → γ -, t' ∝ Γ -, m' ⊢ [ suc j / zero ] P ⊠ Ξ -, m'
