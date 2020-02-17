open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function.Reasoning
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

import Data.Empty as Empty
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Maybe as Maybe
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Bool as Bool
import Data.Fin as Fin
import Data.Fin.Properties as Finₚ
import Data.Vec.Relation.Unary.All as All

open Empty using (⊥-elim)
open Unit using (⊤; tt)
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
    P Q : Scoped n

∋-unused : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
         → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
         → (i : Fin n)
         → (x : γ w Γ ∋ t w m ⊠ Θ)
         → i ≢ toFin x
         → get-mult Γ i ≡ get-mult Θ i
∋-unused zero zero i≢x = ⊥-elim (i≢x refl)
∋-unused zero (suc x) i≢x = refl
∋-unused (suc i) zero i≢x = refl
∋-unused (suc i) (suc x) i≢x = ∋-unused i x (i≢x ∘ cong suc)

⊢-unused : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
         → (i : Fin n)
         → Unused i P
         → γ w Γ ⊢ P ⊠ Θ
         → get-mult Γ i ≡ get-mult Θ i
⊢-unused i uP end = refl
⊢-unused i uP (base ⊢P) = ⊢-unused (suc i) uP ⊢P
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

swap-shape : Fin n → Shapes (suc n) → Shapes (suc n)
swap-shape zero (ss -, y -, x) = ss -, x -, y
swap-shape (suc i) (ss -, z -, y -, x) = swap-shape i (ss -, z -, y) -, x

swap-type : (i : Fin n) → {ss : Shapes (suc n)} → Types ss → Types (swap-shape i ss)
swap-type zero {_ -, _ -, _} (ts -, y -, x) = ts -, x -, y
swap-type (suc i) {_ -, _ -, _ -, _} (ts -, z -, y -, x) = swap-type i (ts -, z -, y) -, x

swap-card : (i : Fin n) → {ss : Shapes (suc n)} → Cards ss → Cards (swap-shape i ss)
swap-card zero {_ -, _ -, _} ((cs , y) , x) = (cs , x) , y
swap-card (suc i) {_ -, _ -, _ -, _} (((cs , z) , y) , x) = swap-card i ((cs , z) , y) , x

swap-mult : (i : Fin n) → {ss : Shapes (suc n)} {cs : Cards ss} → Mults cs → Mults (swap-card i cs)
swap-mult zero {_ -, _ -, _} ((ms , y) , x) = (ms , x) , y
swap-mult (suc i) {_ -, _ -, _ -, _} (((ms , z) , y) , x) = swap-mult i ((ms , z) , y) , x

∋-swap : {ss : Shapes (suc n)} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
       → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
       → (i : Fin n)
       → (x : γ w Γ ∋ t w m ⊠ Θ)
       → Σ[ y ∈ swap-type i γ w swap-mult i Γ ∋ t w m ⊠ swap-mult i Θ ]
         swapFin i (toFin x) ≡ toFin y
∋-swap {γ = _ -, _ -, _} zero zero = suc zero , refl
∋-swap {γ = _ -, _ -, _} zero (suc zero) = zero , refl
∋-swap {γ = _ -, _ -, _} {Γ = (_ , _) , _} zero (suc (suc x)) = suc (suc x) , refl
∋-swap {γ = _ -, _ -, _ -, _} (suc i) zero = zero , refl
∋-swap {γ = _ -, _ -, _ -, _} (suc zero) (suc zero) = suc (suc zero) , refl
∋-swap {γ = _ -, _ -, _ -, _ -, _} (suc (suc zero)) (suc zero) = suc zero , refl
∋-swap {γ = _ -, _ -, _ -, _ -, _} (suc (suc (suc i))) (suc zero) = suc zero , refl
∋-swap {γ = _ -, _ -, _ -, _} (suc i) (suc sx@(suc x)) with ∋-swap i sx
∋-swap {γ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq with Fin.inject₁ i Finₚ.≟ suc (toFin x)
∋-swap {γ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq | yes p = suc x' , suc & trans (suc & (suc & Finₚ.lower₁-irrelevant _ _ _)) eq
∋-swap {γ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq | no ¬p with i Finₚ.≟ (toFin x)
∋-swap {γ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq | no ¬p | yes refl = suc x' , suc & eq
∋-swap {γ = _ -, _ -, _ -, _} (suc i) (suc (suc x)) | x' , eq | no ¬p | no ¬q = suc x' , suc & eq


⊢-swap : {ss : Shapes (suc n)} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
       → (i : Fin n)
       → γ w Γ ⊢ P ⊠ Θ
       → swap-type i γ w swap-mult i Γ ⊢ swap i P ⊠ swap-mult i Θ
⊢-swap {γ = _ -, _ -, _} i end = end
⊢-swap {γ = _ -, _ -, _} i (base ⊢P) = base (⊢-swap (suc i) ⊢P)
⊢-swap {γ = _ -, _ -, _} i (chan t m μ ⊢P) = chan t m μ (⊢-swap (suc i) ⊢P)
⊢-swap {γ = _ -, _ -, _} i (recv x ⊢P) rewrite proj₂ (∋-swap i x) = recv _ (⊢-swap (suc i) ⊢P)
⊢-swap {γ = _ -, _ -, _} i (send x y ⊢P) rewrite proj₂ (∋-swap i x) | proj₂ (∋-swap i y) = send _ _ (⊢-swap i ⊢P)
⊢-swap {γ = _ -, _ -, _} i (comp ⊢P ⊢Q) = comp (⊢-swap i ⊢P) (⊢-swap i ⊢Q)
