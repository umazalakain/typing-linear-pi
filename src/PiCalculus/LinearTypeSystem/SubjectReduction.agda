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
import Data.Fin.Properties as Finₚ

open Empty using (⊥; ⊥-elim)
open Nat using (ℕ; zero; suc)
open Fin using (Fin ; zero ; suc)
open Vec using (Vec; []; _∷_)
open Maybe using (nothing; just)
open Product using (Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)

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
SubjectReduction = {n : ℕ} {γ : PreCtx n} {idxs : Vec I n} {Γ Γ' Δ : Ctx idxs}
                   {c : Channel n} {P Q : Scoped n}
                 → Γ' ≔ channel-1∙ c ⊎ Γ
                 → P =[ c ]⇒ Q
                 → γ ∝ Γ'  ⊢ P ⊠ Δ
                 → γ ∝ Γ   ⊢ Q ⊠ Δ

private
  variable
    n : ℕ
    i j : Fin n
    idxs : Vec I n
    P Q : Scoped n
 
send-≥-∙ : {γ : PreCtx n} {Γ Δ : Ctx idxs}
         → γ ∝ Γ ⊢ i ⟨ j ⟩ P ⊠ Δ → ∃[ y ] (All.lookup i Γ ≔ y ∙ -∙)
send-≥-∙ {Γ = Γ} (send {Δ = Δ} x _ _) = _ , ∙-comm (∋-∙ -∙ x)

recv-≥+∙ : {γ : PreCtx n} {Γ Δ : Ctx idxs}
         → γ ∝ Γ ⊢ i ⦅⦆ P ⊠ Δ → ∃[ y ] (All.lookup i Γ ≔ y ∙ +∙)
recv-≥+∙ (recv x _) = _ , ∙-comm (∋-∙ +∙ x)

comm-≥1∙ : {γ : PreCtx n} {Γ Δ : Ctx idxs} {c : Channel n}
      → P =[ c ]⇒ Q → γ ∝ Γ ⊢ P ⊠ Δ → c ≡ external i → ∃[ y ] (All.lookup i Γ ≔ 1∙ ∙ y)
comm-≥1∙ {i = i} comm (comp (recv x ⊢P) ⊢Q) refl with ⊢-⊎ ⊢P | send-≥-∙ ⊢Q
comm-≥1∙ {i = i} comm (comp (recv x ⊢P) ⊢Q) refl | (_ -, _) , (Ξ≔ , _) | _ , ≥-
  rewrite sym (∙-unique (∙-comm (proj₂ (proj₂ (∙-assoc (∙-comm (∋-∙ +∙ x)) (proj₁ (proj₂ (∙-assoc⁻¹ (⊎-get i Ξ≔) ≥-))))))) (proj₂ ∙-join))
  = _ ,                  ∙-comm (proj₁ (proj₂ (∙-assoc (∙-comm (∋-∙ +∙ x)) (proj₁ (proj₂ (∙-assoc⁻¹ (⊎-get i Ξ≔) ≥-))))))
comm-≥1∙ (par P→P') (comp ⊢P ⊢Q) refl = comm-≥1∙ P→P' ⊢P refl
comm-≥1∙ (res_ {c = internal} P→Q) (chan t m μ ⊢P) ()
comm-≥1∙ (res_ {c = external zero} P→Q) (chan t m μ ⊢P) ()
comm-≥1∙ (res_ {c = external (suc i)} P→Q) (chan t m μ ⊢P) refl = comm-≥1∙ P→Q ⊢P refl
comm-≥1∙ (struct P≅P' P'→Q) ⊢P refl = comm-≥1∙ P'→Q (subject-cong P≅P' ⊢P) refl

align : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ' Γ Δ Θ Ψ : Ctx idxs} {t t'} {idx idx' idx'' idx'''} {m : Cs idx} {m' : Cs idx'}
    → γ       ∝ Γ'      [ i ]≔ C[ t' ∝ m' ] ∝ +∙ {idx''}  ⊠ Θ
    → γ -, t' ∝ Θ -, m' ⊢      P                          ⊠ Δ -, 0∙
    → γ       ∝ Δ       [ i ]≔ C[ t ∝ m ]   ∝ -∙ {idx'''} ⊠ Ψ
    → Γ' ≔ only i 1∙ ⊎ Γ
    → γ -, t' ∝ Γ -, m' ⊢      P                          ⊠ Ψ -, 0∙
align {i = i} {Γ = Γ} {Ψ = Ψ} x ⊢P x' Γ'⇒Γ with ⊢-⊎ ⊢P
align {i = i} {Γ = Γ} {Ψ = Ψ} x ⊢P x' Γ'⇒Γ | (Δ -, _) , (a , b) = ⊢-frame (a , b) (foo  , b) ⊢P
    where

    bar : 1∙ ≔ subst Cs (∋-I x') -∙ ∙ subst Cs (∋-I x) +∙
    bar = subst (λ ● → _ ≔ ● ∙ _) (sym (subst-idx -∙)) (subst (λ ● → _ ≔ _ ∙ ●) (sym (subst-idx +∙)) (∙-comm (proj₂ (∙-join))))

    foo : Γ ≔ Δ ⊎ Ψ
    foo = let _ , c , d = ⊎-assoc (⊎-comm a) (∋-⊎ x')
              _ , e , f = ⊎-assoc (⊎-comm (∋-⊎ x)) (⊎-comm c)
           in subst (λ ● → ● ≔ _ ⊎ _) (⊎-uniqueˡ (subst (λ ● → _ ≔ _ ⊎ ●) (⊎-unique f (only-∙ i bar)) e) (⊎-comm Γ'⇒Γ)) (⊎-comm d)


subject-reduction : SubjectReduction
subject-reduction Γ'⇒Γ comm (comp (recv {P = P} x ⊢P) (send x' y ⊢Q)) = comp (⊢-strengthen zero (subst-unused (λ ()) P) (⊢-subst (align x ⊢P x' Γ'⇒Γ) y)) ⊢Q
subject-reduction Γ'⇒Γ (par P→P') (comp ⊢P ⊢Q) = comp (subject-reduction Γ'⇒Γ P→P' ⊢P) ⊢Q
subject-reduction Γ'⇒Γ (res_ {c = internal} P→Q) (chan t m μ ⊢P) = chan t m μ (subject-reduction (Γ'⇒Γ , ∙-idˡ _) P→Q ⊢P)
subject-reduction Γ'⇒Γ (res_ {c = external zero} P→Q) (chan t m μ ⊢P) = chan t m _ (subject-reduction (Γ'⇒Γ , (proj₂ (comm-≥1∙ P→Q ⊢P refl))) P→Q ⊢P)
subject-reduction Γ'⇒Γ (res_ {c = external (suc i)} P→Q) (chan t m μ ⊢P) = chan t m μ (subject-reduction (Γ'⇒Γ , ∙-idˡ _) P→Q ⊢P)
subject-reduction Γ'⇒Γ (struct P≅P' P'→Q) ⊢P = subject-reduction Γ'⇒Γ P'→Q (subject-cong P≅P' ⊢P)
