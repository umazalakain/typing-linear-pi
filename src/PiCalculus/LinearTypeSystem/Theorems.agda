open import Relation.Binary.PropositionalEquality using (refl)

open import Data.Nat.Base using (ℕ)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_)
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
SubjectCongruence = {n : ℕ} {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs} {P Q : Scoped n}
                  → P ≅ Q
                  → γ w Γ ⊢ P ⊠ Δ
                  → γ w Γ ⊢ Q ⊠ Δ

maybe-consume : {n : ℕ} {ss : Shapes n} {cs : Cards ss} → Mults cs → Channel n → Mults cs
maybe-consume Γ nothing = Γ
maybe-consume {ss = _ -, _} (Γ , m) (just zero) = Γ , replicate ω0
maybe-consume {ss = _ -, _} (Γ , m) (just (suc i)) = maybe-consume Γ (just i) , m

SubjectReduction : Set
SubjectReduction = {n : ℕ} {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
                   {c : Channel n} {P Q : Scoped n}
                 → P =[ c ]⇒ Q
                 → γ w Γ                 ⊢ P ⊠ Δ
                 → γ w maybe-consume Γ c ⊢ Q ⊠ maybe-consume Δ c
