open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
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
open import PiCalculus.Quantifiers

module PiCalculus.LinearTypeSystem.SubjectReduction (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem.Weakening Ω
open import PiCalculus.LinearTypeSystem.Strengthening Ω
open import PiCalculus.LinearTypeSystem.SubjectCongruence Ω

one-at : {n : ℕ} {ss : Shapes n} {cs : Cards ss} → Channel n → Mults cs
one-at nothing = ε
one-at {ss = _ -, _} (just zero) = ε , replicate 1∙
one-at {ss = _ -, _} (just (suc i)) = one-at (just i) , replicate 0∙

SubjectReduction : Set
SubjectReduction = {n : ℕ} {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Γ' Δ Δ' : Mults cs}
                   {c : Channel n} {P Q : Scoped n}
                 → Γ ≡ one-at c ⊎ Γ'
                 → Δ ≡ one-at c ⊎ Δ'
                 → P =[ c ]⇒ Q
                 → γ w Γ ⊢ P ⊠ Δ
                 → γ w Γ' ⊢ Q ⊠ Δ'

private
  variable
    n : ℕ
    P Q : Scoped n

subject-reduction : SubjectReduction
subject-reduction eq refl comm (comp (recv x ⊢P) ⊢Q) = {!comp ? ?!}
subject-reduction {Δ = Δ} {Δ'} {c = nothing} refl refl (par P⇒P') (comp ⊢P ⊢Q) rewrite sym (⊎-idˡ Δ) | sym (⊎-idˡ Δ') = comp (subject-reduction refl refl P⇒P' {!⊢P!}) {!⊢Q!} 
subject-reduction {γ = _ -, _} {c = just i} eq qe (par P⇒P') (comp ⊢P ⊢Q) = comp (subject-reduction refl refl P⇒P' {!⊢P!}) {!⊢Q!}
subject-reduction refl refl (res_ {c = nothing} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ μ (subject-reduction refl refl P⇒Q {!!})
subject-reduction refl refl (res_ {c = just zero} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ 0∙ (subject-reduction refl refl P⇒Q {!!})
subject-reduction refl refl (res_ {c = just (suc i)} P⇒Q) (chan γ δ μ ⊢P) rewrite +-idˡ μ = chan γ δ μ (subject-reduction refl refl P⇒Q {!+-idˡ!})
subject-reduction refl refl (intro_ {c = nothing} P⇒Q) (base ⊢P) = base (subject-reduction refl refl P⇒Q ⊢P)
subject-reduction refl refl (intro_ {c = just zero} P⇒Q) (base ⊢P) = base (subject-reduction refl refl P⇒Q ⊢P)
subject-reduction refl refl (intro_ {c = just (suc x)} P⇒Q) (base ⊢P) = base (subject-reduction refl refl P⇒Q ⊢P)
subject-reduction refl refl (struct P≅P' P'⇒Q) ⊢P = subject-reduction refl refl P'⇒Q (subject-cong P≅P' ⊢P)
