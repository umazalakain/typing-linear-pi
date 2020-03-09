open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toWitness)
open import Function.Reasoning

import Data.Empty as Empty
import Data.Maybe as Maybe
import Data.Nat as Nat
import Data.Bool as Bool
import Data.Fin as Fin
import Data.Product as Product
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All

open Empty using (⊥; ⊥-elim)
open Nat using (ℕ; zero; suc)
open Fin using (Fin ; zero ; suc)
open Vec using (Vec; []; _∷_)
open Maybe using (nothing; just)
open Product using (∃-syntax; _,_; proj₁; proj₂)

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
-- open import PiCalculus.LinearTypeSystem.Substitution Ω
open import PiCalculus.LinearTypeSystem.SubjectCongruence Ω

SubjectReduction : Set
SubjectReduction = {n : ℕ} {γ : PreCtx n} {is : Vec I n} {Γ Γ' Δ : Ctx is}
                   {c : Channel n} {P Q : Scoped n}
                 → Γ ≔ Γ' ⊎ (1∙ at c)
                 → P =[ c ]⇒ Q
                 → γ w Γ  ⊢ P ⊠ Δ
                 → γ w Γ' ⊢ Q ⊠ Δ

private
  variable
    n : ℕ
    i j : Fin n
    is : Vec I n
    P Q : Scoped n

send-≥-∙ : {γ : PreCtx n} {Γ Δ : Ctx is}
         → γ w Γ ⊢ i ⟨ j ⟩ P ⊠ Δ → ∃[ y ] (All.lookup i Γ ≔ y ∙ -∙)
send-≥-∙ (send x _ _) = _ , ∙-comm (∋-∙ -∙ x)

recv-≥+∙ : {γ : PreCtx n} {Γ Δ : Ctx is}
         → γ w Γ ⊢ i ⦅⦆ P ⊠ Δ → ∃[ y ] (All.lookup i Γ ≔ y ∙ +∙)
recv-≥+∙ (recv x _) = _ , ∙-comm (∋-∙ +∙ x)

comm-≥1∙ : {γ : PreCtx n} {Γ Δ : Ctx is} {c : Channel n}
      → P =[ c ]⇒ Q → γ w Γ ⊢ P ⊠ Δ → c ≡ just i → ∃[ y ] (All.lookup i Γ ≔ y ∙ 1∙)
comm-≥1∙ {i = i} comm (comp ⊢P ⊢Q) refl = let _ , ≥+∙ = recv-≥+∙ ⊢P
                                              _ , ≥-∙ = send-≥-∙ ⊢Q
                                              _ , Γ≔  = ⊢-⊎ ⊢P
                                              _ , i≔ , _ = ∙-assoc (∙-comm (⊎-get i Γ≔)) (∙-comm ≥-∙)
                                           in ∙-join ≥+∙ (∙-comm i≔)
comm-≥1∙ (par P→P') (comp ⊢P ⊢Q) refl = comm-≥1∙ P→P' ⊢P refl
comm-≥1∙ (res_ {c = nothing} P→Q) (chan t m μ ⊢P) ()
comm-≥1∙ (res_ {c = just zero} P→Q) (chan t m μ ⊢P) ()
comm-≥1∙ (res_ {c = just (suc i)} P→Q) (chan t m μ ⊢P) refl = comm-≥1∙ P→Q ⊢P refl
comm-≥1∙ (struct P≅P' P'→Q) ⊢P refl = comm-≥1∙ P'→Q (subject-cong P≅P' ⊢P) refl

⊢-recv : {γ : PreCtx n} {Γ Γ' Δ : Ctx is} {uP : Unused zero ([ suc j / zero ] P)}
       → Γ ≔ Γ' ⊎ (+∙ at (just i))
       → γ w Γ  ⊢ i ⦅⦆ P ⊠ Δ
       → γ w Γ' ⊢ lower zero ([ suc j / zero ] P) uP ⊠ Δ
⊢-recv {uP = uP} Γ≔ (recv x ⊢P) = {!!}

subject-reduction : SubjectReduction
subject-reduction Γ≔ comm (comp ⊢P ⊢Q) = comp {!!} {!!}
subject-reduction Γ≔ (par P→P') (comp ⊢P ⊢Q) = comp (subject-reduction Γ≔ P→P' ⊢P) ⊢Q
subject-reduction Γ≔ (res_ {c = nothing} P→Q) (chan t m μ ⊢P) = chan t m μ (subject-reduction (Γ≔ , ∙-idʳ _) P→Q ⊢P)
subject-reduction Γ≔ (res_ {c = just zero} P→Q) (chan t m μ ⊢P) = chan t m _ (subject-reduction (Γ≔ , proj₂ (comm-≥1∙ P→Q ⊢P refl)) P→Q ⊢P)
subject-reduction Γ≔ (res_ {c = just (suc i)} P→Q) (chan t m μ ⊢P) = chan t m μ (subject-reduction (Γ≔ , ∙-idʳ _) P→Q ⊢P)
subject-reduction Γ≔ (struct P≅P' P'→Q) ⊢P = subject-reduction Γ≔ P'→Q (subject-cong P≅P' ⊢P)
