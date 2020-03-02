open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function.Reasoning
open import Relation.Nullary using (yes; no)

import Data.Empty as Empty
import Data.Maybe as Maybe
import Data.Nat as Nat
import Data.Bool as Bool
import Data.Fin as Fin
import Data.Product as Product
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All

open Empty using (⊥-elim)
open Nat using (ℕ; zero; suc)
open Fin using (Fin ; zero ; suc)
open Maybe using (nothing; just)
open Product using (∃-syntax; _,_)

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

1∙-at : {n : ℕ} → Channel n → {γ : PreCtx n} → Ctx γ
1∙-at nothing = ε
1∙-at (just zero) {_ -, _} = ε -, Vec.replicate 1∙
1∙-at (just (suc i)) {_ -, _} = 1∙-at (just i) -, Vec.replicate 0∙

SubjectReduction : Set
SubjectReduction = {n : ℕ} {γ : PreCtx n} {Γ Γ' Δ : Ctx γ}
                   {c : Channel n} {P Q : Scoped n}
                 → Γ ≔ Γ' ⊎ 1∙-at c
                 → P =[ c ]⇒ Q
                 → γ w Γ  ⊢ P ⊠ Δ
                 → γ w Γ' ⊢ Q ⊠ Δ

private
  variable
    n : ℕ
    i : Fin n
    P Q : Scoped n

⊢-≥1∙ : {γ : PreCtx n} {Γ Δ : Ctx γ} {c : Channel n}
      → P =[ c ]⇒ Q → γ w Γ ⊢ P ⊠ Δ → c ≡ just i → ∃[ ys ] (All.lookup i Γ ≔ ys ∙ᵥ Vec.replicate 1∙)
⊢-≥1∙ comm (comp ⊢P ⊢Q) refl = {!!}
⊢-≥1∙ (par P→P') (comp ⊢P ⊢Q) refl = ⊢-≥1∙ P→P' ⊢P refl
⊢-≥1∙ (res_ {c = nothing} P→Q) (chan t m μ ⊢P) ()
⊢-≥1∙ (res_ {c = just zero} P→Q) (chan t m μ ⊢P) ()
⊢-≥1∙ (res_ {c = just (suc i)} P→Q) (chan t m μ ⊢P) refl = ⊢-≥1∙ P→Q ⊢P refl
⊢-≥1∙ (intro_ {c = nothing} P→Q) (base ⊢P) ()
⊢-≥1∙ (intro_ {c = just zero} P→Q) (base ⊢P) ()
⊢-≥1∙ (intro_ {c = just (suc i)} P→Q) (base ⊢P) refl = ⊢-≥1∙ P→Q ⊢P refl
⊢-≥1∙ (struct P≅P' P'→Q) ⊢P refl = ⊢-≥1∙ P'→Q (subject-cong P≅P' ⊢P) refl

subject-reduction : SubjectReduction
subject-reduction Γ≔ comm (comp (recv x ⊢P) ⊢Q) = comp {!⊢P!} {!!}
subject-reduction Γ≔ (par P→P') (comp ⊢P ⊢Q) = comp (subject-reduction Γ≔ P→P' ⊢P) ⊢Q
subject-reduction Γ≔ (res_ {c = nothing} P→Q) (chan t m μ ⊢P)
  = chan t m μ (subject-reduction (Γ≔ , (_ , ∙-idʳ _) , ∙-idʳ _) P→Q ⊢P)
subject-reduction Γ≔ (res_ {c = just zero} P→Q) (chan t m μ ⊢P) = chan t m {!!} (subject-reduction (Γ≔ , ({!!} , {!!})) P→Q ⊢P)
--  = chan t m 0∙ (subject-reduction (Γ≔ , {!(_ , ∙-idˡ _) , ∙-idˡ _!}) (Δ≔ , {!!}) P→Q ⊢P)
subject-reduction Γ≔ (res_ {c = just (suc i)} P→Q) (chan t m μ ⊢P)
  = chan t m μ (subject-reduction (Γ≔ , (_ , ∙-idʳ _) , ∙-idʳ _) P→Q ⊢P)
subject-reduction Γ≔ (intro_ {c = nothing} P→Q) (base ⊢P) = base (subject-reduction (Γ≔ , _) P→Q ⊢P)
subject-reduction Γ≔ (intro_ {c = just zero} P→Q) (base ⊢P) = base (subject-reduction (Γ≔ , _) P→Q ⊢P)
subject-reduction Γ≔ (intro_ {c = just (suc i)} P→Q) (base ⊢P) = base (subject-reduction (Γ≔ , _) P→Q ⊢P)
subject-reduction Γ≔ (struct P≅P' P'→Q) ⊢P = subject-reduction Γ≔ P'→Q (subject-cong P≅P' ⊢P)
{-
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
-}
