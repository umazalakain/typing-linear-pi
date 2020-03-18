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
                 → γ w Γ'  ⊢ P ⊠ Δ
                 → γ w Γ   ⊢ Q ⊠ Δ

private
  variable
    n : ℕ
    i j : Fin n
    idxs : Vec I n
    P Q : Scoped n
 
send-≥-∙ : {γ : PreCtx n} {Γ Δ : Ctx idxs}
         → γ w Γ ⊢ i ⟨ j ⟩ P ⊠ Δ → ∃[ y ] (All.lookup i Γ ≔ y ∙ -∙)
send-≥-∙ {Γ = Γ} (send {Δ = Δ} x _ _) = _ , ∙-comm (∋-∙ -∙ x)

recv-≥+∙ : {γ : PreCtx n} {Γ Δ : Ctx idxs}
         → γ w Γ ⊢ i ⦅⦆ P ⊠ Δ → ∃[ y ] (All.lookup i Γ ≔ y ∙ +∙)
recv-≥+∙ (recv x _) = _ , ∙-comm (∋-∙ +∙ x)

comm-≥1∙ : {γ : PreCtx n} {Γ Δ : Ctx idxs} {c : Channel n}
      → P =[ c ]⇒ Q → γ w Γ ⊢ P ⊠ Δ → c ≡ external i → ∃[ y ] (All.lookup i Γ ≔ 1∙ ∙ y)
comm-≥1∙ {i = i} (comm refl) (comp (recv x ⊢P) ⊢Q) refl with ⊢-⊎ ⊢P | send-≥-∙ ⊢Q
comm-≥1∙ {i = i} (comm refl) (comp (recv x ⊢P) ⊢Q) refl | (_ -, _) , (Ξ≔ , _) | _ , ≥-
  rewrite sym (∙-unique (∙-comm (proj₂ (proj₂ (∙-assoc (∙-comm (∋-∙ +∙ x)) (proj₁ (proj₂ (∙-assoc⁻¹ (⊎-get i Ξ≔) ≥-))))))) (proj₂ ∙-join))
  = _ ,                  ∙-comm (proj₁ (proj₂ (∙-assoc (∙-comm (∋-∙ +∙ x)) (proj₁ (proj₂ (∙-assoc⁻¹ (⊎-get i Ξ≔) ≥-))))))
comm-≥1∙ (par P→P') (comp ⊢P ⊢Q) refl = comm-≥1∙ P→P' ⊢P refl
comm-≥1∙ (res_ {c = internal} P→Q) (chan t m μ ⊢P) ()
comm-≥1∙ (res_ {c = external zero} P→Q) (chan t m μ ⊢P) ()
comm-≥1∙ (res_ {c = external (suc i)} P→Q) (chan t m μ ⊢P) refl = comm-≥1∙ P→Q ⊢P refl
comm-≥1∙ (struct P≅P' P'→Q) ⊢P refl = comm-≥1∙ P'→Q (subject-cong P≅P' ⊢P) refl

tor : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ' Δ Θ Ψ : Ctx idxs} {t t'} {idx idx' idx'' idx'''} {m : Cs idx} {m' : Cs idx'}
    → (x  : γ w Γ' ∋ C[ t' w m' ] w +∙ {idx''} ⊠ Θ)
    → (x' : γ w Δ ∋ C[ t w m ] w -∙ {idx'''} ⊠ Ψ)
    → toFin x ≡ toFin x'
    → idx' ≡ idx
tor zero zero refl = refl
tor (suc x) (suc y) eq = tor x y (Finₚ.suc-injective eq)

ert : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ' Δ Θ Ψ : Ctx idxs} {t t'} {idx idx' idx'' idx'''} {m : Cs idx} {m' : Cs idx'}
    → (x  : γ w Γ' ∋ C[ t' w m' ] w +∙ {idx''} ⊠ Θ)
    → (x' : γ w Δ ∋ C[ t w m ] w -∙ {idx'''} ⊠ Ψ)
    → (eq : toFin x ≡ toFin x')
    → m ≡ subst Cs (tor x x' eq) m'
ert zero zero refl = refl
ert (suc x) (suc y) eq = ert x y (Finₚ.suc-injective eq)

bar : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ' Γ Δ Θ Ψ : Ctx idxs} {t t'} {idx idx' idx'' idx'''} {m : Cs idx} {m' : Cs idx'}
    → (x  : γ w Γ' ∋ C[ t' w m' ] w +∙ {idx''} ⊠ Θ)
    → γ -, t' w Θ -, m' ⊢ P ⊠ Δ -, 0∙
    → (x' : γ w Δ ∋ C[ t w m ] w -∙ {idx'''} ⊠ Ψ)
    → Γ' ≔ only (toFin x) 1∙ ⊎ Γ
    → toFin x ≡ toFin x'
    → γ -, t' w Γ -, m' ⊢ P ⊠ Ψ -, 0∙
bar {Γ = Γ} {Ψ = Ψ} x ⊢P x' Γ'⇒Γ eq with ⊢-⊎ ⊢P
bar {Γ = Γ} {Ψ = Ψ} x ⊢P x' Γ'⇒Γ eq | (Δ -, _) , (a , b) = ⊢-frame (a , b) (foo  , b) ⊢P
    where

    ret : {idxs : Vec I n} {Γ : Ctx idxs} {i j : Fin n} {idxa idxb : I}
        → i ≡ j
        → (eqa : idxa ≡ Vec.lookup idxs i)
        → (eqb : idxb ≡ Vec.lookup idxs j)
        → Γ ≔ only i (subst Cs eqa (+∙ {idxa})) ⊎ only j (subst Cs eqb (-∙ {idxb}))
        → Γ ≔ only i +∙ ⊎ only i -∙
    ret refl eqa eqb s = s |> subst (λ ● → _ ≔ only _ ● ⊎ _) (subst-idx +∙) |> subst (λ ● → _ ≔ _ ⊎ only _ ●) (subst-idx -∙)

    foo : Γ ≔ Δ ⊎ Ψ
    foo = let _ , c , d = ⊎-assoc (⊎-comm a) (∋-⊎ x')
              _ , e , f = ⊎-assoc (⊎-comm (∋-⊎ x)) (⊎-comm c)
           in subst (λ ● → ● ≔ _ ⊎ _) (⊎-uniqueˡ (subst (λ ● → _ ≔ _ ⊎ ●) (⊎-unique (ret eq (∋-I x) (∋-I x') (⊎-comm f)) (only-∙ (toFin x) (proj₂ ∙-join))) e) (⊎-comm Γ'⇒Γ)) (⊎-comm d)

postulate
  tar : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ Ξ Ψ : Ctx idxs} {t t'} {idx idx'}  {m : Cs idx} {m' : Cs idx'}
      → γ -, t' w Γ -, m' ⊢ P ⊠ Ψ -, 0∙
      → (y : γ w Ψ ∋ t w m ⊠ Ξ)
      → γ -, t' w Γ -, m' ⊢ [ suc (toFin y) / zero ] P ⊠ Ξ -, m'

  foo : ∀ {γ : PreCtx n} {idxs : Vec I n} {Γ' Γ Δ Ξ Θ Ψ : Ctx idxs} {t t'} {idx idx' idx'' idx'''} {m : Cs idx} {m' : Cs idx'}
      → (x  : γ w Γ' ∋ C[ t' w m' ] w +∙ {idx''} ⊠ Θ)
      → γ -, t' w Θ -, m' ⊢ P ⊠ Δ -, 0∙
      → (x' : γ w Δ ∋ C[ t w m ] w -∙ {idx'''} ⊠ Ψ)
      → (y : γ w Ψ ∋ t w m ⊠ Ξ)
      → Γ' ≔ only (toFin x) 1∙ ⊎ Γ
      → toFin x ≡ toFin x'
      → γ w Γ ⊢ lower zero ([ suc (toFin y) / zero ] P) (subst-unused (λ ()) P) ⊠ Ξ

subject-reduction : SubjectReduction
subject-reduction Γ'⇒Γ (comm eq) (comp (recv {P = P} x ⊢P) (send x' y ⊢Q)) = comp (⊢-strengthen zero (subst-unused (λ ()) P) (tar (bar x ⊢P x' Γ'⇒Γ eq) y)) ⊢Q
subject-reduction Γ'⇒Γ (par P→P') (comp ⊢P ⊢Q) = comp (subject-reduction Γ'⇒Γ P→P' ⊢P) ⊢Q
subject-reduction Γ'⇒Γ (res_ {c = internal} P→Q) (chan t m μ ⊢P) = chan t m μ (subject-reduction (Γ'⇒Γ , ∙-idˡ _) P→Q ⊢P)
subject-reduction Γ'⇒Γ (res_ {c = external zero} P→Q) (chan t m μ ⊢P) = chan t m _ (subject-reduction (Γ'⇒Γ , (proj₂ (comm-≥1∙ P→Q ⊢P refl))) P→Q ⊢P)
subject-reduction Γ'⇒Γ (res_ {c = external (suc i)} P→Q) (chan t m μ ⊢P) = chan t m μ (subject-reduction (Γ'⇒Γ , ∙-idˡ _) P→Q ⊢P)
subject-reduction Γ'⇒Γ (struct P≅P' P'→Q) ⊢P = subject-reduction Γ'⇒Γ P'→Q (subject-cong P≅P' ⊢P)
