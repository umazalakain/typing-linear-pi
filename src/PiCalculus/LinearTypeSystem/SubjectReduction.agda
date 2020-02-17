open import Relation.Binary.PropositionalEquality using (subst)
open import Function.Reasoning

import Data.Maybe as Maybe
import Data.Nat as Nat
import Data.Bool as Bool
import Data.Fin as Fin
import Data.Product as Product

open Nat using (ℕ; zero; suc)
open Fin using (Fin ; zero ; suc)
open Maybe using (nothing; just)
open Product using (_,_)

open import PiCalculus.Syntax
open Scoped
open Syntax
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.SubjectReduction (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem.Weakening Ω
open import PiCalculus.LinearTypeSystem.Strengthening Ω
open import PiCalculus.LinearTypeSystem.SubjectCongruence Ω

maybe-consume : {n : ℕ} {ss : Shapes n} {cs : Cards ss} → Mults cs → Channel n → Mults cs
maybe-consume Γ nothing = Γ
maybe-consume {ss = _ -, _} (Γ , m) (just zero) = Γ , replicate 0∙
maybe-consume {ss = _ -, _} (Γ , m) (just (suc i)) = maybe-consume Γ (just i) , m

SubjectReduction : Set
SubjectReduction = {n : ℕ} {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
                   {c : Channel n} {P Q : Scoped n}
                 → P =[ c ]⇒ Q
                 → γ w Γ                 ⊢ P ⊠ Δ
                 → γ w maybe-consume Γ c ⊢ Q ⊠ maybe-consume Δ c

private
  variable
    n : ℕ
    P Q : Scoped n

subject-reduction : SubjectReduction
subject-reduction comm (comp (recv x ⊢P) ⊢Q) = {!⊢Q!}
subject-reduction {c = nothing} (par P⇒P') (comp ⊢P ⊢Q) = comp (subject-reduction P⇒P' ⊢P) ⊢Q
subject-reduction {γ = _ -, _} {c = just i} (par P⇒P') (comp ⊢P ⊢Q) = comp (subject-reduction P⇒P' ⊢P) {!!}
subject-reduction (res_ {c = nothing} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ μ (subject-reduction P⇒Q ⊢P)
subject-reduction (res_ {c = just zero} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ 0∙ (subject-reduction P⇒Q ⊢P)
subject-reduction (res_ {c = just (suc i)} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ μ (subject-reduction P⇒Q ⊢P)
subject-reduction (intro_ {c = nothing} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (intro_ {c = just zero} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (intro_ {c = just (suc x)} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (struct P≅P' P'⇒Q) ⊢P = subject-reduction P'⇒Q (subject-cong P≅P' ⊢P)
