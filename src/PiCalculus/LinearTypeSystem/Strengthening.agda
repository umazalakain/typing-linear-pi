open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Function.Reasoning
open import Function using (_∘_)

import Data.Empty as Empty
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Bool as Bool
import Data.Fin as Fin
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
open import PiCalculus.Quantifiers

module PiCalculus.LinearTypeSystem.Strengthening (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    P Q : Scoped n

delete-mult : {γ : PreCtx (suc n)} → Ctx γ → (i : Fin (suc n)) → Ctx (Vec.remove γ i)
delete-mult (Γ -, _) zero = Γ
delete-mult (Γ -, ys -, xs) (suc i) = delete-mult (Γ -, ys) i -, xs

∋-strengthen : {γ : PreCtx (suc n)} {Γ Θ : Ctx γ}
             → {i' : I} {t' : Type} {m' : Usage (i' , t')}
             → (i : Fin (suc n))
             → (  x : γ               w Γ               ∋ t' w m' ⊠ Θ)
             → (i≢x : i ≢ toFin x)
             → Σ[ y ∈ Vec.remove γ i w delete-mult Γ i ∋ t' w m' ⊠ delete-mult Θ i ]
               Fin.punchOut i≢x ≡ toFin y
∋-strengthen zero zero i≢x = ⊥-elim (i≢x refl)
∋-strengthen zero (suc x) i≢x = x , refl
∋-strengthen {Γ = _ -, _ -, _} (suc i) zero i≢x = zero , refl
∋-strengthen {Γ = _ -, _ -, _} (suc i) (suc x) i≢x with ∋-strengthen i x (i≢x ∘ cong suc)
∋-strengthen {Γ = _ -, _ -, _} {Θ = _ -, _ -, _} (suc i) (suc x) i≢x | x' , eq = suc x' , cong suc eq

⊢-strengthen : {γ : PreCtx (suc n)} {Γ Θ : Ctx γ}
             → {P : Scoped (suc n)}
             → (i : Fin (suc n))
             → (uP : Unused i P)
             → γ w Γ ⊢ P ⊠ Θ
             → Vec.remove γ i w delete-mult Γ i ⊢ lower i P uP ⊠ delete-mult Θ i
⊢-strengthen i uP end = end
⊢-strengthen {Γ = _ -, _} {Θ = _ -, _} i uP (base ⊢P)
  = base (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {Γ = _ -, _} {Θ = _ -, _} i uP (chan t m μ ⊢P)
  = chan t m μ (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {Γ = _ -, _} {Θ = _ -, _} i (i≢x , uP) (recv {Ξ = _ -, _} x ⊢P)
  rewrite proj₂ (∋-strengthen i x i≢x)
  = recv _ (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {γ = _ -, _} i (i≢x , i≢y , uP) (send x y ⊢P)
  rewrite proj₂ (∋-strengthen i x i≢x) | proj₂ (∋-strengthen i y i≢y)
  = send _ _ (⊢-strengthen i uP ⊢P)
⊢-strengthen {γ = _ -, _} i (uP , uQ) (comp ⊢P ⊢Q)
  = comp (⊢-strengthen i uP ⊢P) (⊢-strengthen i uQ ⊢Q)
