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
open All using (All; []; _∷_)
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
SubjectReduction = {n : ℕ} {γ : PreCtx n} {idxs : Idxs n} {idx : Idx} {Γ Γ' Ξ : Ctx idxs}
                   {c : Channel n} {P Q : Scoped n}
                 → maybe (Γ' ≡ Γ) (λ i → Γ' ≔ ℓ# {idx} at i ⊠ Γ) c
                 → P =[ c ]⇒ Q
                 → γ ∝ Γ'  ⊢ P ⊠ Ξ
                 → γ ∝ Γ   ⊢ Q ⊠ Ξ

private
  variable
    n : ℕ
    i j : Fin n
    idxs : Idxs n
    P Q : Scoped n

extract-ℓ# : {Γ Ξ Δ Ψ Θ : Ctx idxs} {idx' idx'' : Idx}
           → Γ ≔ ℓᵢ {idx'} at i ⊠ Ξ
           → Ψ ≔ ℓₒ {idx''} at i ⊠ Θ
           → Ξ ≔ Δ ⊎ Ψ
           → ∃[ z ] (All.lookup i Γ ≔ ℓ# ∙² z)
extract-ℓ# (zero x) (zero y) (_ , s) =
  let
    ⁇ , Ξ≔ℓₒ∙⁇ , _ = ∙²-assoc (∙²-comm s) y
    _ , Γ≔[ℓᵢℓₒ]∙⁇ , [ℓᵢℓₒ]≔ℓᵢ∙ℓₒ = ∙²-assoc⁻¹ x Ξ≔ℓₒ∙⁇
    ℓ#≡ℓᵢℓₒ = ∙²-unique [ℓᵢℓₒ]≔ℓᵢ∙ℓₒ (∙-idʳ , ∙-idˡ)
  in _ , subst (λ ● → _ ≔ ● ∙² ⁇) ℓ#≡ℓᵢℓₒ Γ≔[ℓᵢℓₒ]∙⁇
extract-ℓ# (suc i) (suc o) (s , _) = extract-ℓ# i o s

-- What we have: Γ' ---ℓᵢ--> Θ ---P--> Ξ ---ℓₒ--> Ψ
-- What we need: Γ' ---ℓ#--> Γ ---P--> Ψ
align : ∀ {γ : PreCtx n} {idxs : Idxs n} {Γ' Γ Ξ Θ Ψ : Ctx idxs} {idx' idx'' idx'''}
    → Γ' ≔ ℓᵢ {idx'} at i ⊠ Θ
    → Ξ  ≔ ℓₒ {idx''} at i ⊠ Ψ
    → Γ' ≔ ℓ# {idx'''} at i ⊠ Γ
    → γ ∝ Θ ⊢ P ⊠ Ξ
    → γ ∝ Γ ⊢ P ⊠ Ψ
align i o io ⊢P with Only-≡Idx io | Only-≡Idx i | Only-≡Idx o
align i o io ⊢P | refl | refl | refl =
  let
  Δi , Γ'≔Δi∙Θ , Δi≔ℓᵢ = Only-⊎ i
  Δo , Ξ≔Δo∙Ψ , Δo≔ℓₒ = Only-⊎ o
  Δio , Γ'≔Δio∙Γ , Δio≔ℓ# = Only-⊎ io
  Δ⊢P , Θ≔Δ⊢P∙Ξ = ⊢-⊎ ⊢P
  ΨΔ⊢P , Θ≔Δo∙[ΨΔ⊢P] , ΨΔ⊢P≔Ψ∙Δ⊢P = ⊎-assoc (⊎-comm Θ≔Δ⊢P∙Ξ) Ξ≔Δo∙Ψ
  ΔiΔo , Γ'≔[ΔiΔo]∙[ΨΔ⊢P] , ΔiΔo≔ℓᵢℓₒ = ⊎-assoc⁻¹ Γ'≔Δi∙Θ Θ≔Δo∙[ΨΔ⊢P]
  Δio≔Δi∙Δo = only-∙ Δio≔ℓ# Δi≔ℓᵢ Δo≔ℓₒ (∙-idʳ , ∙-idˡ)
  ΔiΔo≡Δio = ⊎-unique ΔiΔo≔ℓᵢℓₒ Δio≔Δi∙Δo
  Γ'≔Δio∙[ΨΔ⊢P] = subst (λ ● → _ ≔ ● ⊎ _) ΔiΔo≡Δio Γ'≔[ΔiΔo]∙[ΨΔ⊢P]
  ΨΔ⊢P≡Γ = ⊎-uniqueˡ (⊎-comm Γ'≔Δio∙[ΨΔ⊢P]) (⊎-comm Γ'≔Δio∙Γ)
  Γ≔Ψ∙Δ⊢P = subst (λ ● → ● ≔ _ ⊎ _) ΨΔ⊢P≡Γ ΨΔ⊢P≔Ψ∙Δ⊢P
  in ⊢-frame Θ≔Δ⊢P∙Ξ (⊎-comm Γ≔Ψ∙Δ⊢P) ⊢P

comm-≥ℓ# : {γ : PreCtx n} {Γ Δ : Ctx idxs} {c : Channel n}
      → P =[ c ]⇒ Q → γ ∝ Γ ⊢ P ⊠ Δ → c ≡ external i → ∃[ y ] (All.lookup i Γ ≔ ℓ# ∙² y)
comm-≥ℓ# {i = i} comm (comp (recv x ⊢P) (send x' _ ⊢Q)) refl with ⊢-⊎ ⊢P
comm-≥ℓ# {i = i} comm (comp (recv x ⊢P) (send x' _ ⊢Q)) refl | (_ -, _) , (Ξ≔ , _)
  = extract-ℓ# (∋-Only x) (∋-Only x') Ξ≔
comm-≥ℓ# (par P→P') (comp ⊢P ⊢Q) refl = comm-≥ℓ# P→P' ⊢P refl
comm-≥ℓ# (res_ {c = internal} P→Q) (chan t m μ ⊢P) ()
comm-≥ℓ# (res_ {c = external zero} P→Q) (chan t m μ ⊢P) ()
comm-≥ℓ# (res_ {c = external (suc i)} P→Q) (chan t m μ ⊢P) refl = comm-≥ℓ# P→Q ⊢P refl
comm-≥ℓ# (struct P≅P' P'→Q) ⊢P refl = comm-≥ℓ# P'→Q (subject-cong P≅P' ⊢P) refl

subject-reduction : SubjectReduction
subject-reduction Γ'⇒Γ comm (comp (recv {P = P} x ⊢P) (send x' y ⊢Q)) with trans (sym (∋-≡Type x)) (∋-≡Type x')
subject-reduction Γ'⇒Γ comm (comp (recv {P = P} x ⊢P) (send x' y ⊢Q)) | refl = comp ⊢P' ⊢Q
  where ⊢P' = ⊢P
            |> align (suc (∋-Only x)) (suc (∋-Only x')) (suc Γ'⇒Γ)
            |> ⊢-subst y
            |> ⊢-strengthen zero (subst-unused (λ ()) P)
subject-reduction Γ'⇒Γ (par P→P') (comp ⊢P ⊢Q) = comp (subject-reduction Γ'⇒Γ P→P' ⊢P) ⊢Q
subject-reduction {idx = idx} refl (res_ {c = internal} P→Q) (chan t m μ ⊢P)
  = chan t m μ (subject-reduction {idx = idx} refl P→Q ⊢P)
subject-reduction refl (res_ {c = external zero} P→Q) (chan t m μ ⊢P)
  = let (lμ' , rμ') , (ls , rs) = comm-≥ℓ# P→Q ⊢P refl
        rs' = subst (λ ● → _ ≔ _ ∙ ●) (∙-uniqueˡ (∙-comm rs) (∙-comm ls)) rs
     in chan t m lμ' (subject-reduction (zero (ls , rs')) P→Q ⊢P)
subject-reduction Γ'⇒Γ (res_ {c = external (suc i)} P→Q) (chan t m μ ⊢P)
  = chan t m μ (subject-reduction (suc Γ'⇒Γ) P→Q ⊢P)
subject-reduction Γ'⇒Γ (struct P≅P' P'→Q) ⊢P = subject-reduction Γ'⇒Γ P'→Q (subject-cong P≅P' ⊢P)
