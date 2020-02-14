{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (yes; no)
open import Function.Reasoning

import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Fin as Fin
import Data.Vec.Relation.Unary.All as All

open Unit using (⊤; tt)
open Nat using (ℕ; zero; suc)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Function
open import PiCalculus.Syntax
open Scoped
open Syntax
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.OmegaNat
open import PiCalculus.LinearTypeSystem.ContextLemmas
open import PiCalculus.LinearTypeSystem.Framing

module PiCalculus.LinearTypeSystem.SubjectCongruence where

SubjectCongruence : Set
SubjectCongruence = {n : ℕ} {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs} {P Q : Scoped n}
                  → P ≅ Q
                  → γ w Γ ⊢ P ⊠ Δ
                  → γ w Γ ⊢ Q ⊠ Δ

private
  variable
    n : ℕ
    P Q : Scoped n

comp-comm : {ss : Shapes n} {cs : Cards ss} {γ : Types ss}
          → (Γ Ξ : Mults cs)
          → γ w Γ ⊢ P ∥ Q ⊠ Ξ
          → γ w Γ ⊢ Q ∥ P ⊠ Ξ
comp-comm Γ Ξ (comp ⊢P ⊢Q) with ⊢-⊆ ⊢P | ⊢-⊆ ⊢Q
comp-comm Γ Ξ (comp ⊢P ⊢Q) | l , refl | r , refl = comp
  (⊢Q |> ⊢-frame (Ξ ⊎ l) refl              ∶ _ w (Ξ ⊎ l) ⊎ r ⊢ _ ⊠ (Ξ ⊎ l)
      |> subst (λ ●                        → _ w ●           ⊢ _ ⊠ (Ξ ⊎ l))
        (trans (⊎-assoc _ _ _)
        (trans (_⊎_ & refl ⊗ ⊎-comm _ _)
               (sym (⊎-assoc _ _ _))))     ∶ _ w (Ξ ⊎ r) ⊎ l ⊢ _ ⊠ (Ξ ⊎ l))
  (⊢P |> ⊢-frame _ refl                    ∶ _ w Ξ ⊎ l       ⊢ _ ⊠ Ξ)


subject-cong : SubjectCongruence
subject-cong comp-assoc (comp ⊢P (comp ⊢Q ⊢R)) = comp (comp ⊢P ⊢Q) ⊢R
subject-cong comp-symm (comp ⊢P ⊢Q) = comp-comm _ _ (comp ⊢P ⊢Q)
subject-cong comp-end (comp ⊢P end) = ⊢P
subject-cong scope-end (chan t c μ ⊢P) = {!⊢P!}
subject-cong base-end (base end) = end
subject-cong (scope-ext u) (chan t c μ (comp ⊢P ⊢Q)) = comp {!!} {!!}
subject-cong (base-ext u) (base (comp ⊢P ⊢Q)) = comp {!!} {!!}
subject-cong scope-scope-comm (chan t c μ (chan t₁ c₁ μ₁ ⊢P)) = chan t₁ c₁ μ₁ (chan t c μ {!!})
subject-cong scope-base-comm (chan t c μ (base ⊢P)) = base (chan t c μ {!!})
subject-cong base-base-comm (base (base ⊢P)) = {!!}
subject-cong cong-refl ⊢P = ⊢P
subject-cong (cong-symm comp-assoc) (comp (comp ⊢P ⊢Q) ⊢R) = comp ⊢P (comp ⊢Q ⊢R)
subject-cong (cong-symm comp-symm) (comp ⊢P ⊢Q) = {!!}
subject-cong (cong-symm comp-end) ⊢P = comp ⊢P end
subject-cong (cong-symm scope-end) ⊢P = chan B[ 0 ] [] 0∙ {!end!}
subject-cong (cong-symm base-end) ⊢P = base {!end!}
subject-cong (cong-symm (scope-ext u)) (comp ⊢P (chan t c μ ⊢Q)) = {!!}
subject-cong (cong-symm (base-ext u)) (comp ⊢P (base ⊢Q)) = {!!}
subject-cong (cong-symm scope-scope-comm) (chan t c μ (chan t₁ c₁ μ₁ ⊢P)) = {!!}
subject-cong (cong-symm scope-base-comm) (base (chan t c μ ⊢P)) = {!!}
subject-cong (cong-symm base-base-comm) (base (base ⊢P)) = {!!}
subject-cong (cong-symm cong-refl) ⊢P = ⊢P
subject-cong (cong-symm (cong-symm P≅Q)) ⊢P = subject-cong P≅Q ⊢P
subject-cong (cong-symm (new-cong P≅Q)) (chan t c μ ⊢P) = chan t c μ (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (comp-cong P≅Q)) (comp ⊢P ⊢R) = comp (subject-cong (cong-symm P≅Q) ⊢P) ⊢R
subject-cong (cong-symm (input-cong P≅Q)) (recv x ⊢P) = recv x (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (output-cong P≅Q)) (send x y ⊢P) = send x y (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (base-cong P≅Q)) (base ⊢P) = base (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (new-cong P≅Q) (chan t c μ ⊢P) = chan t c μ (subject-cong P≅Q ⊢P)
subject-cong (comp-cong P≅Q) (comp ⊢P ⊢R) = comp (subject-cong P≅Q ⊢P) ⊢R
subject-cong (input-cong P≅Q) (recv x ⊢P) = recv x (subject-cong P≅Q ⊢P)
subject-cong (output-cong P≅Q) (send x y ⊢P) = send x y (subject-cong P≅Q ⊢P)
subject-cong (base-cong P≅Q) (base ⊢P) = base (subject-cong P≅Q ⊢P)
