open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl; sym; subst; cong; trans)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

import Data.Empty as Empty
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Fin as Fin
import Data.Fin.Properties as Finₚ
import Data.Vec.Relation.Unary.All as All

open Empty using (⊥-elim)
open Nat using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Swapping (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    i j : Fin n
    idx : Idx
    idxs : Idxs n
    P Q : Scoped n

∋-unused : {γ : PreCtx n} {Γ Θ : Ctx idxs} {t : Type} {x : Carrier idx ²}
         → (i : Fin n)
         → γ ∝ Γ [ j ]≔ t ∝ x ⊠ Θ
         → i ≢ j
         → All.lookup i Γ ≡ All.lookup i Θ
∋-unused zero zero i≢x = ⊥-elim (i≢x refl)
∋-unused zero (suc x) i≢x = refl
∋-unused (suc i) zero i≢x = refl
∋-unused (suc i) (suc x) i≢x = ∋-unused i x (i≢x ∘ cong suc)

⊢-unused : {γ : PreCtx n} {Γ Θ : Ctx idxs}
         → (i : Fin n)
         → Unused i P
         → γ ∝ Γ ⊢ P ⊠ Θ
         → All.lookup i Γ ≡ All.lookup i Θ
⊢-unused i uP end = refl
⊢-unused i uP (chan t m μ ⊢P) = ⊢-unused (suc i) uP ⊢P
⊢-unused i (i≢x , uP) (recv x ⊢P) = trans
  (∋-unused i x i≢x)
  (⊢-unused (suc i) uP ⊢P)
⊢-unused i (i≢x , i≢y , uP) (send x y ⊢P) = trans (trans
  (∋-unused i x i≢x)
  (∋-unused i y i≢y))
  (⊢-unused i uP ⊢P)
⊢-unused i (uP , uQ) (comp ⊢P ⊢Q) = trans
  (⊢-unused i uP ⊢P)
  (⊢-unused i uQ ⊢Q)

module _ {a} {A : Set a} where
  swapᵥ : (i : Fin n) → Vec A (suc n) → Vec A (suc n)
  swapᵥ zero (xs -, y -, x) = xs -, x -, y
  swapᵥ (suc i) (xs -, y -, x) = swapᵥ i (xs -, y) -, x

  swapₐ : ∀ {b} {P : A → Set b} (i : Fin n) {xs : Vec A (suc n)} → All P xs → All P (swapᵥ i xs)
  swapₐ zero (xs -, y -, x) = xs -, x -, y
  swapₐ (suc i) (xs -, y -, x) = swapₐ i (xs -, y) -, x

-- TODO: rewrite this crap
∋-swap : {γ : PreCtx (suc n)} {idxs : Idxs (suc n)} {Γ Θ : Ctx idxs} {t : Type} {x : Carrier idx ²}
       → (i : Fin n)
       → γ ∝ Γ [ j ]≔ t ∝ x ⊠ Θ
       → swapᵥ i γ ∝ swapₐ i Γ [ swapFin i j ]≔ t ∝ x ⊠ swapₐ i Θ
∋-swap {γ = _ -, _ -, _} {idxs = _ -, _ -, _} {Γ = _ -, _ -, _} zero zero = suc zero
∋-swap {γ = _ -, _ -, _} zero (suc zero) = zero
∋-swap {γ = _ -, _ -, _} zero (suc (suc x)) = suc (suc x)
∋-swap {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) zero = zero
∋-swap {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc zero) (suc zero) = suc (suc zero)
∋-swap {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc (suc i)) (suc zero) = suc zero
∋-swap {j = suc (suc j)} {γ = γ -, _} {Γ = Γ -, _} (suc i) (suc (suc x)) with Fin.inject₁ i Finₚ.≟ suc j
∋-swap {j = suc (suc j)} {γ = γ -, _} {Γ = Γ -, _} (suc zero) (suc (suc x)) | yes ()
∋-swap {j = suc (suc ._)} {γ = γ -, _} {Γ = Γ -, _} {Θ = Θ -, _} (suc (suc i)) (suc sx@(suc x)) | yes refl = suc ((subst (λ ● → swapᵥ (suc i) γ ∝ swapₐ (suc i) Γ [ ● ]≔ _ ∝ _ ⊠ swapₐ (suc i) Θ) (sym (trans (cong suc (sym (trans (swapFin-injectˡ i) (cong suc (sym (Finₚ.lower₁-inject₁′ i _)))))) (swapFin-suc i (Fin.inject₁ i)))) (∋-swap (suc i) sx)))
∋-swap {j = suc (suc j)} {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (suc sx@(suc x)) | no ¬p with i Finₚ.≟ j
∋-swap {j = suc (suc j)} {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (suc sx@(suc x)) | no ¬p | yes refl rewrite sym (swapFin-injectʳ i) = suc (∋-swap i sx)
∋-swap {j = suc (suc j)} {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) (suc sx@(suc x)) | no ¬p | no ¬q rewrite sym (swapFin-neq i j ¬q ¬p) = suc (∋-swap i sx)

⊢-swap : {γ : PreCtx (suc n)} {Γ Θ : Ctx idxs}
       → (i : Fin n)
       → γ ∝ Γ ⊢ P ⊠ Θ
       → swapᵥ i γ ∝ swapₐ i Γ ⊢ swap i P ⊠ swapₐ i Θ
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i end = end
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (chan t m μ ⊢P) = chan t m μ (⊢-swap (suc i) ⊢P)
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (recv {Ξ = _ -, _ -, _} x ⊢P) = recv (∋-swap i x) (⊢-swap (suc i) ⊢P)
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (send x y ⊢P) = send (∋-swap i x) (∋-swap i y) (⊢-swap i ⊢P)
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (comp ⊢P ⊢Q) = comp (⊢-swap i ⊢P) (⊢-swap i ⊢Q)
