open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)
open import Function.Reasoning

import Data.Empty as Empty
import Data.Maybe as Maybe
import Data.Nat as Nat
import Data.Bool as Bool
import Data.Fin as Fin
import Data.Product as Product
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
import Data.Fin.Properties as Finₚ

open Empty using (⊥; ⊥-elim)
open Nat using (ℕ; zero; suc)
open Fin using (Fin ; zero ; suc)
open Vec using (Vec; []; _∷_)
open Maybe using (nothing; just)
open Product using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)

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
open import PiCalculus.LinearTypeSystem.Framing Ω
open import PiCalculus.LinearTypeSystem.Weakening Ω
open import PiCalculus.LinearTypeSystem.Strengthening Ω
open import PiCalculus.LinearTypeSystem.Substitution Ω
open import PiCalculus.LinearTypeSystem.SubjectCongruence Ω

SubjectReduction : Set
SubjectReduction = {n : ℕ} {γ : PreCtx n} {idxs : Idxs n} {Γ Γ' Δ : Ctx idxs}
                   {c : Channel n} {P Q : Scoped n}
                 → Γ' ≔ channel-ℓ# c ⊎ Γ
                 → P =[ c ]⇒ Q
                 → γ ∝ Γ'  ⊢ P ⊠ Δ
                 → γ ∝ Γ   ⊢ Q ⊠ Δ

private
  variable
    n : ℕ
    i j : Fin n
    idxs : Idxs n
    P Q : Scoped n

tar : {idx : Idx} {Γᵢ y Ξᵢ Δᵢ Θᵢ z Ψᵢ x : Carrier idx ²}
    → Γᵢ ≔ y ∙² Ξᵢ
    → Ξᵢ ≔ Δᵢ ∙² Θᵢ
    → Θᵢ ≔ z ∙² Ψᵢ
    → x ≔ y ∙² z
    → ∃[ δ ] (Γᵢ ≔ x ∙² δ)
tar Γᵢ Ξᵢ Θᵢ x = let q , a , b = ∙²-assoc (∙²-comm Ξᵢ) Θᵢ
                     _ , c , d = ∙²-assoc (∙²-comm Γᵢ) (∙²-comm a)
                  in q , subst (λ ● → _ ≔ ● ∙² _) (∙²-unique (∙²-comm d) x) (∙²-comm c)

comm-≥ℓ# : {γ : PreCtx n} {Γ Δ : Ctx idxs} {c : Channel n}
      → P =[ c ]⇒ Q → γ ∝ Γ ⊢ P ⊠ Δ → c ≡ external i → ∃[ y ] (All.lookup i Γ ≔ ℓ# ∙² y)
comm-≥ℓ# {i = i} comm (comp (recv x ⊢P) (send x' _ ⊢Q)) refl with ⊢-⊎ ⊢P
comm-≥ℓ# {i = i} comm (comp (recv x ⊢P) (send x' _ ⊢Q)) refl | (_ -, _) , (Ξ≔ , _) =
  tar (∋-∙ (1∙ , 0∙) x) (⊎-get i Ξ≔) (∋-∙ (0∙ , 1∙) x') (∙-idʳ _ , ∙-idˡ _)
comm-≥ℓ# (par P→P') (comp ⊢P ⊢Q) refl = comm-≥ℓ# P→P' ⊢P refl
comm-≥ℓ# (res_ {c = internal} P→Q) (chan t m μ ⊢P) ()
comm-≥ℓ# (res_ {c = external zero} P→Q) (chan t m μ ⊢P) ()
comm-≥ℓ# (res_ {c = external (suc i)} P→Q) (chan t m μ ⊢P) refl = comm-≥ℓ# P→Q ⊢P refl
comm-≥ℓ# (struct P≅P' P'→Q) ⊢P refl = comm-≥ℓ# P'→Q (subject-cong P≅P' ⊢P) refl

align : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ' Γ Δ Θ Ψ : Ctx idxs} {t t'} {idx idx' idx'' idx'''} {m : Carrier idx ²} {m' : Carrier idx' ²}
    → γ       ∝ Γ'      [ i ]≔ C[ t' ∝ m' ] ∝ ℓᵢ {idx''}  ⊠ Θ
    → γ -, t' ∝ Θ -, m' ⊢      P                          ⊠ Δ -, ℓ∅
    → γ       ∝ Δ       [ i ]≔ C[ t ∝ m ]   ∝ ℓₒ {idx'''} ⊠ Ψ
    → Γ' ≔ only i ℓ# ⊎ Γ
    → γ -, t' ∝ Γ -, m' ⊢      P                          ⊠ Ψ -, ℓ∅
align {i = i} {Γ = Γ} {Ψ = Ψ} x ⊢P x' Γ'⇒Γ with ⊢-⊎ ⊢P
align {i = i} {Γ = Γ} {Ψ = Ψ} x ⊢P x' Γ'⇒Γ | (Δ -, _) , (a , b) = ⊢-frame (a , b) (foo  , b) ⊢P
    where

    bar : (1∙ , 1∙) ≔ subst (λ i → Carrier i ²) (∋-I x') ℓₒ ∙² subst (λ i → Carrier i ²) (∋-I x) ℓᵢ
    bar = subst (λ ● → _ ≔ ● ∙² _) {!!} (subst (λ ● → _ ≔ _ ∙² ●) {!? , ?!} (∙²-comm (∙-idʳ _ , ∙-idˡ _)))

    foo : Γ ≔ Δ ⊎ Ψ
    foo = let _ , c , d = ⊎-assoc (⊎-comm a) (∋-⊎ x')
              _ , e , f = ⊎-assoc (⊎-comm (∋-⊎ x)) (⊎-comm c)
           in subst (λ ● → ● ≔ _ ⊎ _) (⊎-uniqueˡ (subst (λ ● → _ ≔ _ ⊎ ●) (⊎-unique f (only-∙ i bar)) e) (⊎-comm Γ'⇒Γ)) (⊎-comm d)


subject-reduction : SubjectReduction
subject-reduction Γ'⇒Γ comm (comp (recv {P = P} x ⊢P) (send x' y ⊢Q))
  = comp (⊢-strengthen zero (subst-unused (λ ()) P) (⊢-subst (align x ⊢P x' Γ'⇒Γ) y)) ⊢Q
subject-reduction Γ'⇒Γ (par P→P') (comp ⊢P ⊢Q) = comp (subject-reduction Γ'⇒Γ P→P' ⊢P) ⊢Q
subject-reduction Γ'⇒Γ (res_ {c = internal} P→Q) (chan t m μ ⊢P)
  = chan t m μ (subject-reduction (Γ'⇒Γ , ∙²-idˡ _) P→Q ⊢P)
subject-reduction Γ'⇒Γ (res_ {c = external zero} P→Q) (chan t m μ ⊢P)
  = let (lμ' , rμ') , (ls , rs) = comm-≥ℓ# P→Q ⊢P refl
        rs' = subst (λ ● → _ ≔ _ ∙ ●) (∙-uniqueˡ (∙-comm rs) (∙-comm ls)) rs
     in chan t m lμ' (subject-reduction (Γ'⇒Γ , ls , rs') P→Q ⊢P)
subject-reduction Γ'⇒Γ (res_ {c = external (suc i)} P→Q) (chan t m μ ⊢P)
  = chan t m μ (subject-reduction (Γ'⇒Γ , ∙²-idˡ _) P→Q ⊢P)
subject-reduction Γ'⇒Γ (struct P≅P' P'→Q) ⊢P = subject-reduction Γ'⇒Γ P'→Q (subject-cong P≅P' ⊢P)
