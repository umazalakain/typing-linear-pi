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
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Strengthening (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    is : Vec I n
    P Q : Scoped n

∋-strengthen : {γ : PreCtx (suc n)} {is : Vec I (suc n)} {Γ Θ : Ctx is}
             → {i' : I} {t' : Type} {m' : Cs i'}
             → (i : Fin (suc n))
             → (  x : γ               ∝ Γ               ∋ t' ∝ m' ⊠ Θ)
             → (i≢x : i ≢ toFin x)
             → Σ[ y ∈ Vec.remove γ i ∝ mult-remove Γ i ∋ t' ∝ m' ⊠ mult-remove Θ i ]
               Fin.punchOut i≢x ≡ toFin y
∋-strengthen zero zero i≢x = ⊥-elim (i≢x refl)
∋-strengthen zero (suc x) i≢x = x , refl
∋-strengthen {γ = _ -, _ -, _} {_ -, _ -, _} {_ -, _ -, _} (suc i) zero i≢x = zero , refl
∋-strengthen {γ = _ -, _ -, _} {_ -, _ -, _} {_ -, _ -, _} (suc i) (suc x) i≢x with ∋-strengthen i x (i≢x ∘ cong suc)
∋-strengthen {γ = _ -, _ -, _} {_ -, _ -, _} {_ -, _ -, _} {_ -, _ -, _} (suc i) (suc x) i≢x | x' , eq = suc x' , cong suc eq

⊢-strengthen : {γ : PreCtx (suc n)} {is : Vec I (suc n)} {Γ Θ : Ctx is}
             → {P : Scoped (suc n)}
             → (i : Fin (suc n))
             → (uP : Unused i P)
             → γ ∝ Γ ⊢ P ⊠ Θ
             → Vec.remove γ i ∝ mult-remove Γ i ⊢ lower i P uP ⊠ mult-remove Θ i
⊢-strengthen i uP end = end
⊢-strengthen {γ = _ -, _} {Γ = _ -, _} {Θ = _ -, _} i uP (chan t m μ ⊢P)
  = chan t m μ (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {γ = _ -, _} {Γ = _ -, _} {Θ = _ -, _} i (i≢x , uP) (recv {Ξ = _ -, _} x ⊢P)
  rewrite proj₂ (∋-strengthen i x i≢x)
  = recv _ (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {γ = _ -, _} i (i≢x , i≢y , uP) (send x y ⊢P)
  rewrite proj₂ (∋-strengthen i x i≢x) | proj₂ (∋-strengthen i y i≢y)
  = send _ _ (⊢-strengthen i uP ⊢P)
⊢-strengthen {γ = _ -, _} i (uP , uQ) (comp ⊢P ⊢Q)
  = comp (⊢-strengthen i uP ⊢P) (⊢-strengthen i uQ ⊢Q)
