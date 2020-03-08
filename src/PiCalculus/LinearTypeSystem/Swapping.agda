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
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Swapping (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    j : I
    is : Vec I n
    P Q : Scoped n

∋-unused : {γ : PreCtx n} {Γ Θ : Ctx is} {t : Type} {xs : Cs j}
         → (i : Fin n)
         → (x : γ w Γ ∋ t w xs ⊠ Θ)
         → i ≢ toFin x
         → All.lookup i Γ ≡ All.lookup i Θ
∋-unused zero zero i≢x = ⊥-elim (i≢x refl)
∋-unused zero (suc x) i≢x = refl
∋-unused (suc i) zero i≢x = refl
∋-unused (suc i) (suc x) i≢x = ∋-unused i x (i≢x ∘ cong suc)

⊢-unused : {γ : PreCtx n} {Γ Θ : Ctx is}
         → (i : Fin n)
         → Unused i P
         → γ w Γ ⊢ P ⊠ Θ
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
∋-swap : {γ : PreCtx (suc n)} {is : Vec I (suc n)} {Γ Θ : Ctx is} {t : Type} {xs : Cs j}
       → (i : Fin n)
       → (x : γ w Γ ∋ t w xs ⊠ Θ)
       → Σ[ y ∈ swapᵥ i γ w swapₐ i Γ ∋ t w xs ⊠ swapₐ i Θ ]
         swapFin i (toFin x) ≡ toFin y
∋-swap {γ = _ -, _ -, _} {is = _ -, _ -, _} {Γ = _ -, _ -, _} zero zero = suc zero , refl
∋-swap {Γ = _ -, _ -, _} zero (suc zero) = zero , refl
∋-swap {Γ = _ -, _ -, _} zero (suc (suc x)) = suc (suc x) , refl
∋-swap {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc i) zero = zero , refl
∋-swap {γ = _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _} (suc zero) (suc zero) = suc (suc zero) , refl
∋-swap {γ = _ -, _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _ -, _} (suc (suc zero)) (suc zero) = suc zero , refl
∋-swap {γ = _ -, _ -, _ -, _ -, _} {Γ = _ -, _ -, _ -, _ -, _} (suc (suc (suc i))) (suc zero) = suc zero , refl
∋-swap {Γ = _ -, _ -, _ -, _} (suc i) (suc sx@(suc x)) with ∋-swap i sx
∋-swap {Γ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq with Fin.inject₁ i Finₚ.≟ suc (toFin x)
∋-swap {Γ = _ -, _ -, _ -, _} {Θ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq | yes p = suc x' , suc & trans (suc & (suc & Finₚ.lower₁-irrelevant _ _ _)) eq
∋-swap {Γ = _ -, _ -, _ -, _} {Θ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq | no ¬p with i Finₚ.≟ (toFin x)
∋-swap {Γ = _ -, _ -, _ -, _} {Θ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq | no ¬p | yes refl = suc x' , suc & eq
∋-swap {Γ = _ -, _ -, _ -, _} {Θ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq | no ¬p | no ¬q = suc x' , suc & eq

⊢-swap : {γ : PreCtx (suc n)} {Γ Θ : Ctx is}
       → (i : Fin n)
       → γ w Γ ⊢ P ⊠ Θ
       → swapᵥ i γ w swapₐ i Γ ⊢ swap i P ⊠ swapₐ i Θ
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i end = end
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (chan t m μ ⊢P) = chan t m μ (⊢-swap (suc i) ⊢P)
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (recv {Ξ = _ -, _ -, _} x ⊢P) rewrite proj₂ (∋-swap i x) = recv _ (⊢-swap (suc i) ⊢P)
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (send x y ⊢P) rewrite proj₂ (∋-swap i x) | proj₂ (∋-swap i y) = send _ _ (⊢-swap i ⊢P)
⊢-swap {γ = _ -, _ -, _} {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} i (comp ⊢P ⊢Q) = comp (⊢-swap i ⊢P) (⊢-swap i ⊢Q)
