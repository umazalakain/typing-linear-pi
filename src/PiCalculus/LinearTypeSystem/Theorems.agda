open import Relation.Binary.PropositionalEquality using (refl)

open import Data.Nat.Base using (ℕ)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ-syntax)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (nothing; just)
open import Level using (Level) renaming (suc to lsuc)

import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
open Vec using (Vec)

open import PiCalculus.Syntax
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.OmegaNat
open Scoped

module PiCalculus.LinearTypeSystem.Theorems where

SubjectCongruence : Set
SubjectCongruence = {n : ℕ} {ss : SCtx n} {γ : TCtx ss} {Γ Δ : CCtx ss} {P Q : Scoped n}
                  → P ≅ Q
                  → γ w Γ ⊢ P ⊠ Δ
                  → γ w Γ ⊢ Q ⊠ Δ

maybe-consume : {n : ℕ} {ss : SCtx n} → CCtx ss → Channel n → CCtx ss
maybe-consume Γ nothing = Γ
maybe-consume (Γ -, μs) (just zero) = Γ -, Vec.map consume μs
maybe-consume (Γ -, μs) (just (suc i)) = maybe-consume Γ (just i) -, μs

SubjectReduction : Set
SubjectReduction = {n : ℕ} {ss : SCtx n} {γ : TCtx ss} {Γ Δ : CCtx ss}
                   {c : Channel n} {P Q : Scoped n}
                 → P =[ c ]⇒ Q
                 → γ w Γ                 ⊢ P ⊠ Δ
                 → γ w maybe-consume Γ c ⊢ Q ⊠ maybe-consume Δ c
