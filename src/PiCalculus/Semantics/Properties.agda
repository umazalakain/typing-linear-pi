{-# OPTIONS --safe #-} -- --without-K #-}

open import Function using (_∘_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)

import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
import Data.Fin as Fin
import Data.Fin.Properties as Finₚ

open ℕ using (ℕ; zero; suc)
open Fin using (Fin; zero; suc)

open import PiCalculus.Syntax
open Scoped
open import PiCalculus.Semantics

module PiCalculus.Semantics.Properties where
private
  variable
    n : ℕ
    i j : Fin n
    P : Scoped n

lift-lower : (i : Fin (suc n)) (P : Scoped (suc n)) (uP : Unused i P)
           → lift i (lower i P uP) ≡ P
lift-lower i 𝟘 uP = refl
lift-lower i (υ P) uP
  rewrite lift-lower (suc i) P uP = refl
lift-lower i (P ∥ Q) (uP , uQ)
  rewrite lift-lower i P uP
  | lift-lower i Q uQ = refl
lift-lower i (x ⦅⦆ P) (i≢x , uP)
  rewrite lift-lower (suc i) P uP
  | Finₚ.punchIn-punchOut i≢x = refl
lift-lower i (x ⟨ y ⟩ P) (i≢x , i≢y , uP)
  rewrite lift-lower i P uP
  | Finₚ.punchIn-punchOut i≢x
  | Finₚ.punchIn-punchOut i≢y = refl

substFin-suc : (i j x : Fin n) → (suc x) [ suc i ↦ suc j ]' ≡ suc (x [ i ↦ j ]')
substFin-suc i j x with i Finₚ.≟ x
substFin-suc i j x | yes p = refl
substFin-suc i j x | no ¬p = refl

swapFin-suc : (i : Fin n) (x : Fin (suc n)) → suc (swapFin i x) ≡ swapFin (suc i) (suc x)
swapFin-suc i x with Fin.inject₁ i Finₚ.≟ x
swapFin-suc i .(Fin.inject₁ i) | yes refl = cong suc (cong suc (Finₚ.lower₁-irrelevant _ _ _))
swapFin-suc i x | no ¬p with (suc i) Fin.≟ x
swapFin-suc i x | no ¬p | yes q = refl
swapFin-suc i x | no ¬p | no ¬q = refl

swapFin-injectˡ : (i : Fin n) → swapFin i (Fin.inject₁ i) ≡ suc i
swapFin-injectˡ zero = refl
swapFin-injectˡ (suc i) rewrite sym (swapFin-suc i (Fin.inject₁ i)) = cong suc (swapFin-injectˡ i)

swapFin-injectʳ : (i : Fin n) → swapFin i (suc i) ≡ Fin.inject₁ i
swapFin-injectʳ zero = refl
swapFin-injectʳ (suc i) rewrite sym (swapFin-suc i (suc i)) = cong suc (swapFin-injectʳ i)

swapFin-neq : (i j : Fin n) → i ≢ j → Fin.inject₁ i ≢ suc j → swapFin i (suc j) ≡ suc j
swapFin-neq zero zero i≢j ii≢sj = ⊥-elim (i≢j refl)
swapFin-neq zero (suc zero) i≢j ii≢sj = refl
swapFin-neq zero (suc (suc j)) i≢j ii≢sj = refl
swapFin-neq (suc zero) zero i≢j ii≢sj = ⊥-elim (ii≢sj refl)
swapFin-neq (suc (suc i)) zero i≢j ii≢sj = refl
swapFin-neq (suc i) (suc j) i≢j ii≢sj
  rewrite sym (swapFin-suc i (suc j))
  = cong suc (swapFin-neq i j (i≢j ∘ cong suc) (ii≢sj ∘ cong suc))

swapFin-swapFin : ∀ (i : Fin n) (x : Fin (suc n)) → swapFin i (swapFin i x) ≡ x
swapFin-swapFin i x with Fin.inject₁ i Fin.≟ x
swapFin-swapFin i x | yes p with Fin.inject₁ i Finₚ.≟ (suc (Fin.lower₁ x (notMax i x p)))
swapFin-swapFin i .(Fin.inject₁ i) | yes refl | yes q = ⊥-elim (ℕₚ.1+n≢n (begin
  suc (Fin.toℕ i)                              ≡˘⟨ cong (suc ∘ Fin.toℕ) (Finₚ.lower₁-inject₁ i) ⟩
  suc (Fin.toℕ (Fin.lower₁ (Fin.inject₁ i) _)) ≡⟨ cong (suc ∘ Fin.toℕ) (Finₚ.lower₁-irrelevant _ _ _) ⟩
  suc (Fin.toℕ (Fin.lower₁ (Fin.inject₁ i) _)) ≡˘⟨ cong Fin.toℕ q ⟩
  Fin.toℕ (Fin.inject₁ i)                      ≡⟨ Finₚ.toℕ-inject₁ i ⟩
  Fin.toℕ i                                    ∎
  ))
swapFin-swapFin i x | yes p | no ¬q with i Finₚ.≟ Fin.lower₁ x (notMax i x p)
swapFin-swapFin i x | yes p | no ¬q | yes r = p
swapFin-swapFin i x | yes refl | no ¬q | no ¬r = ⊥-elim (¬r (begin
  i                            ≡˘⟨ Finₚ.lower₁-inject₁ i ⟩
  Fin.lower₁ (Fin.inject₁ i) _ ≡⟨ Finₚ.lower₁-irrelevant _ _ _ ⟩
  Fin.lower₁ (Fin.inject₁ i) _ ∎))
swapFin-swapFin i x | no ¬p with (suc i) Fin.≟ x
swapFin-swapFin i x | no ¬p | yes q with Fin.inject₁ i Fin.≟ Fin.inject₁ i
swapFin-swapFin i x | no ¬p | yes refl | yes refl = begin
  suc (Fin.lower₁ (Fin.inject₁ i) _)
    ≡⟨ cong suc (Finₚ.lower₁-irrelevant _ _ _) ⟩
  suc (Fin.lower₁ (Fin.inject₁ i) _)
    ≡⟨ cong suc (Finₚ.lower₁-inject₁ i) ⟩
  suc i
    ∎
swapFin-swapFin i x | no ¬p | yes q | no ¬r = ⊥-elim (¬r refl)
swapFin-swapFin i x | no ¬p | no ¬q with Fin.inject₁ i Fin.≟ x
swapFin-swapFin i x | no ¬p | no ¬q | yes r = ⊥-elim (¬p r)
swapFin-swapFin i x | no ¬p | no ¬q | no ¬r with (suc i) Fin.≟ x
swapFin-swapFin i x | no ¬p | no ¬q | no ¬r | yes s = ⊥-elim (¬q s)
swapFin-swapFin i x | no ¬p | no ¬q | no ¬r | no ¬s = refl

swap-swap : ∀ (i : Fin n) (P : Scoped (suc n)) → swap i (swap i P) ≡ P
swap-swap i 𝟘 = refl
swap-swap i (υ P) rewrite swap-swap (suc i) P = refl
swap-swap i (P ∥ Q) rewrite swap-swap i P | swap-swap i Q = refl
swap-swap i (x ⦅⦆ P) rewrite swapFin-swapFin i x | swap-swap (suc i) P = refl
swap-swap i (x ⟨ y ⟩ P) rewrite swapFin-swapFin i x | swapFin-swapFin i y | swap-swap i P = refl
