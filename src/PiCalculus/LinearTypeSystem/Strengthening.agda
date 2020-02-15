open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function.Reasoning
open import Function using (_∘_)

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
open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.OmegaNat
open import PiCalculus.LinearTypeSystem.ContextLemmas

module PiCalculus.LinearTypeSystem.Strengthening where

private
  variable
    n : ℕ
    P Q : Scoped n

delete-type : {ss : Shapes (suc n)} (i : Fin (suc n)) → Types ss → Types (Vec.remove ss i)
delete-type zero (ts -, t) = ts
delete-type (suc i) (ts -, t' -, t) = delete-type i (ts -, t') -, t

delete-card : {ss : Shapes (suc n)} (i : Fin (suc n)) → Cards ss → Cards (Vec.remove ss i)
delete-card {ss = _ -, _} zero (cs , c) = cs
delete-card {ss = _ -, _ -, _} (suc i) (cs , c) = delete-card i cs , c

delete-mult : {ss : Shapes (suc n)} {cs : Cards ss} (i : Fin (suc n)) → Mults cs → Mults (delete-card i cs)
delete-mult {ss = _ -, _} zero (ms , m) = ms
delete-mult {ss = _ -, _ -, _} (suc i) (ms , m) = delete-mult i ms , m

∋-strengthen : {ss : Shapes (suc n)} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
             → {s' : Shape} {c' : Card s'} {t' : Type s'} {m' : Mult s' c'}
             → (i : Fin (suc n))
             → (  x : γ               w Γ               ∋ t' w m' ⊠ Θ)
             → (i≢x : i ≢ toFin x)
             → Σ[ y ∈ delete-type i γ w delete-mult i Γ ∋ t' w m' ⊠ delete-mult i Θ ]
               Fin.punchOut i≢x ≡ toFin y
∋-strengthen zero zero i≢x = ⊥-elim (i≢x refl)
∋-strengthen zero (suc x) i≢x = x , refl
∋-strengthen {γ = _ -, _ -, _} (suc i) zero i≢x = zero , refl
∋-strengthen {γ = _ -, _ -, _} (suc i) (suc x) i≢x with ∋-strengthen i x (i≢x ∘ cong suc)
∋-strengthen {γ = _ -, _ -, _} (suc i) (suc x) i≢x | x' , eq = suc x' , cong suc eq

⊢-strengthen : {ss : Shapes (suc n)} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
             → {P : Scoped (suc n)}
             → (i : Fin (suc n))
             → (uP : Unused i P)
             → γ w Γ ⊢ P ⊠ Θ
             → delete-type i γ w delete-mult i Γ ⊢ lower i P uP ⊠ delete-mult i Θ
⊢-strengthen {γ = _ -, _} i uP end = end
⊢-strengthen {γ = _ -, _} i uP (base ⊢P)
  = base (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {γ = _ -, _} i uP (chan t m μ ⊢P)
  = chan t m μ (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {γ = _ -, _} i (i≢x , uP) (recv x ⊢P)
  rewrite proj₂ (∋-strengthen i x i≢x)
  = recv _ (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {γ = _ -, _} i (i≢x , i≢y , uP) (send x y ⊢P)
  rewrite proj₂ (∋-strengthen i x i≢x)
  | proj₂ (∋-strengthen i y i≢y)
  = send _ _ (⊢-strengthen i uP ⊢P)
⊢-strengthen {γ = _ -, _} i (uP , uQ) (comp ⊢P ⊢Q)
  = comp (⊢-strengthen i uP ⊢P) (⊢-strengthen i uQ ⊢Q)
