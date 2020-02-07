open import Agda.Builtin.Reflection

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Relation.Nullary using (_because_; yes; no; does)
open import Level using () renaming (zero to lzero)
open import Data.Unit.Base using (tt; ⊤)

import Level
import Data.Maybe.Base as Maybe
import Data.Nat.Base as ℕ
import Data.Bool.Base as Bool
import Data.List.Base as List
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
import Data.Fin.Properties as Finₚ
import Data.Nat.Properties as ℕₚ
import Data.Product as Product

open ℕ using (ℕ)
open Vec using ([]; _∷_)
open Fin using (Fin)
open Bool using (Bool; true; false; if_then_else_; _∧_)
open List using (_∷_; [])
open Maybe using (Maybe; nothing; just)
open Product using (_×_; _,_)

open import PiCalculus.Function
open import PiCalculus.Semantics using (swapFin)
open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.ContextLemmas

module PiCalculus.LinearTypeSystem.SubstSolver where

{-# DISPLAY Vec.lookup Γ i = Γ [ i ] #-}
{-# DISPLAY Vec.updateAt i f Γ = Γ [ f / i ] #-}

pattern ⟨_⟩ x = arg (arg-info visible relevant) x
pattern ⟪_⟫ x = arg (arg-info hidden relevant) x
-- TODO: use nary functions
pattern _`[_/_] Γ x i = def (quote _[_/_]) (⟪ _ ⟫ ∷ ⟪ _ ⟫ ∷ ⟨ Γ ⟩ ∷ ⟨ x ⟩ ∷ ⟨ i ⟩ ∷ [])
pattern _`[_] Γ i = def (quote _[_]) (⟪ _ ⟫ ∷ ⟪ _ ⟫ ∷ ⟨ Γ ⟩ ∷ ⟨ i ⟩ ∷ [])
pattern _`≡_ x y = (def (quote _≡_) (⟪ _ ⟫ ∷ ⟪ _ ⟫ ∷ ⟨ x ⟩ ∷ ⟨ y ⟩ ∷ []))
pattern _`&_ f eq = (def (quote _&_) (⟨ f ⟩ ∷ ⟨ eq ⟩ ∷ []))
pattern _`⊗_ ep eq = (def (quote _⊗_) (⟨ ep ⟩ ∷ ⟨ eq ⟩ ∷ []))
pattern `refl = con (quote refl) []
pattern `sym x≡y = def (quote sym) (⟨ x≡y ⟩ ∷ [])
pattern `trans x≡y y≡z = def (quote trans) (⟨ x≡y ⟩ ∷ ⟨ y≡z ⟩ ∷ [])
pattern `_ i = var i []
infixr 50 `_
infixl 9 _`&_
infixl 8 _`⊗_

module _ where
  Proof : Set
  Proof = Term

  open import Data.Maybe.Base using (_>>=_; _<∣>_) renaming (map to _<$>_)

  _is_ : ℕ → ℕ → Bool
  n is m = does (n ℕₚ.≟ m)

  simplify : Term → Term × Proof

  -- get ∘ set
  simplify t@(Γ `[ x / ` i ] `[ ` j ])
    = let (x' , p) = simplify x
       in (x' , `trans (def (quote subst-get) (⟨ Γ ⟩ ∷ ⟨ ` j ⟩ ∷ [])) p)

  simplify t@(Γ `[ Δ / ` j ]) with simplify Γ | simplify Δ
  -- set ∘ get
  simplify t@(Γ `[ Δ / ` j ]) | Γ' , p | Ω `[ ` i ] , q
    = Γ' , `trans (def (quote _[_/_]) [] `& p `⊗ q `⊗ `refl)
                  (def (quote subst-id) (⟨ Γ' ⟩ ∷ ⟨ ` i ⟩ ∷ []))
  -- congruence on _[_/_]
  simplify t@(Γ `[ Δ / ` j ]) | Γ' , p | Δ' , q = (Γ' `[ Δ' / ` j ]) , def (quote _[_/_]) [] `& p `⊗ q `⊗ `refl

  -- give up
  simplify t = t , `refl

  equational : Term → Proof
  equational t@(x `≡ y) with simplify x | simplify y
  ... | (_ , p) | (_ , q) = `trans p (`sym q)
  equational t = t


module _ where
  _>>=_ = bindTC
  macro
    solve : (Term → Proof) → Term → TC ⊤
    solve solver hole = do goal ← inferType hole
                           unify hole (solver goal)

module Test {ℓ n} (Γ : Context {ℓ} n) (i : Fin n) (σ : Elem) where
  test-get : Γ [ Γ [ σ / i ] [ i ] / i ] [ i ] ≡ σ
  test-get = solve equational

  test-get-cong : Γ [ Γ [ Γ [ i ] / i ] [ i ] / i ] [ i ] ≡ Γ [ i ]
  test-get-cong = solve equational

  test-set-conf : (Γ [ Γ [ i ] / i ]) [ Γ [ σ / i ] [ i ] / i ] ≡ Γ [ σ / i ]
  test-set-conf = solve equational

  test-id : Γ [ Γ [ i ] / i ] [ Γ [ i ] / i ] ≡ Γ
  test-id = solve equational

swap-input-context : ∀ {ℓ n σ } (Γ : Context {ℓ} n) (i j x : Fin n)
     → Γ [ σ / x ] [ Γ [ σ / x ] [ i ] / j ] [ Γ [ σ / x ] [ j ] / i ]
     ≡ Γ [ Γ [ i ] / j ] [ Γ [ j ] / i ] [ σ / swapFin i j x ]
swap-input-context Γ i j x with i Finₚ.≟ x
swap-input-context Γ .x j x | yes refl with j Finₚ.≟ x
swap-input-context Γ .x j x | yes refl | no j≢x = {!solve basic!}
swap-input-context Γ .x .x x | yes refl | yes refl = {!solve equational !}
swap-input-context Γ i j x | no i≢x with j Finₚ.≟ x
swap-input-context Γ i j x | no i≢x | no j≢x = {!!}
swap-input-context Γ i .x x | no i≢x | yes refl = {!!}
