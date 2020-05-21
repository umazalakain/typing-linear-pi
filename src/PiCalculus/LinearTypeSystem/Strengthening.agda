{-# OPTIONS --safe #-} -- --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
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
open Product using (_,_; proj₁; proj₂)

import PiCalculus.Syntax
open PiCalculus.Syntax.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Algebras

module PiCalculus.LinearTypeSystem.Strengthening (Ω : Algebras) where
open Algebras Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    idxs : Idxs n
    idx idx' : Idx
    t t' : Type
    i j : Fin n
    P Q : Scoped n

∋-strengthen : {γ : PreCtx (suc n)} {idxs : Idxs (suc n)} {Γ Θ : Ctx idxs} {m' : Usage idx' ²}
             → (i : Fin (suc n))
             → (i≢j : i ≢ j)
             → γ              ； Γ              ∋[ j ] t' ； m' ⊠ Θ
             → Vec.remove γ i ； ctx-remove Γ i ∋[ Fin.punchOut i≢j ] t' ； m' ⊠ ctx-remove Θ i
∋-strengthen zero i≢x (zero , zero _) = ⊥-elim (i≢x refl)
∋-strengthen zero i≢x (suc t , suc x) = t , x
∋-strengthen {γ = _ -, _ -, _} {_ -, _ -, _} {_ -, _ -, _} (suc i) i≢x (zero , zero xyz) = zero , zero xyz
∋-strengthen {γ = _ -, _ -, _} {_ -, _ -, _} {_ -, _ -, _} {_ -, _ -, _} (suc i) i≢x (suc t , suc x) = there (∋-strengthen i (i≢x ∘ cong suc) (t , x))

⊢-strengthen : {P : Scoped (suc n)} {γ : PreCtx (suc n)} {idxs : Idxs (suc n)} {Γ Θ : Ctx idxs}
             → (i : Fin (suc n))
             → (uP : Unused i P)
             → γ ； Γ ⊢ P ⊠ Θ
             → Vec.remove γ i ； ctx-remove Γ i ⊢ lower i P uP ⊠ ctx-remove Θ i
⊢-strengthen i uP end = end
⊢-strengthen {γ = _ -, _} {Γ = _ -, _} {Θ = _ -, _} i uP (chan t m μ ⊢P)
  = chan t m μ (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {γ = _ -, _} {Γ = _ -, _} {Θ = _ -, _} i (i≢x , uP) (recv {Ξ = _ -, _} x ⊢P)
  = recv (∋-strengthen i i≢x x) (⊢-strengthen (suc i) uP ⊢P)
⊢-strengthen {γ = _ -, _} i (i≢x , i≢y , uP) (send x y ⊢P)
  = send (∋-strengthen i i≢x x) (∋-strengthen i i≢y y) (⊢-strengthen i uP ⊢P)
⊢-strengthen {γ = _ -, _} i (uP , uQ) (comp ⊢P ⊢Q)
  = comp (⊢-strengthen i uP ⊢P) (⊢-strengthen i uQ ⊢Q)
