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
lift-lower i (ν P) uP
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

exchangeFin-suc : (i : Fin n) (x : Fin (suc n)) → suc (exchangeFin i x) ≡ exchangeFin (suc i) (suc x)
exchangeFin-suc i x with Fin.inject₁ i Finₚ.≟ x
exchangeFin-suc i .(Fin.inject₁ i) | yes refl = cong suc (cong suc (Finₚ.lower₁-irrelevant _ _ _))
exchangeFin-suc i x | no ¬p with (suc i) Fin.≟ x
exchangeFin-suc i x | no ¬p | yes q = refl
exchangeFin-suc i x | no ¬p | no ¬q = refl

exchangeFin-injectˡ : (i : Fin n) → exchangeFin i (Fin.inject₁ i) ≡ suc i
exchangeFin-injectˡ zero = refl
exchangeFin-injectˡ (suc i) rewrite sym (exchangeFin-suc i (Fin.inject₁ i)) = cong suc (exchangeFin-injectˡ i)

exchangeFin-injectʳ : (i : Fin n) → exchangeFin i (suc i) ≡ Fin.inject₁ i
exchangeFin-injectʳ zero = refl
exchangeFin-injectʳ (suc i) rewrite sym (exchangeFin-suc i (suc i)) = cong suc (exchangeFin-injectʳ i)

exchangeFin-neq : (i j : Fin n) → i ≢ j → Fin.inject₁ i ≢ suc j → exchangeFin i (suc j) ≡ suc j
exchangeFin-neq zero zero i≢j ii≢sj = ⊥-elim (i≢j refl)
exchangeFin-neq zero (suc zero) i≢j ii≢sj = refl
exchangeFin-neq zero (suc (suc j)) i≢j ii≢sj = refl
exchangeFin-neq (suc zero) zero i≢j ii≢sj = ⊥-elim (ii≢sj refl)
exchangeFin-neq (suc (suc i)) zero i≢j ii≢sj = refl
exchangeFin-neq (suc i) (suc j) i≢j ii≢sj
  rewrite sym (exchangeFin-suc i (suc j))
  = cong suc (exchangeFin-neq i j (i≢j ∘ cong suc) (ii≢sj ∘ cong suc))

exchangeFin-exchangeFin : ∀ (i : Fin n) (x : Fin (suc n)) → exchangeFin i (exchangeFin i x) ≡ x
exchangeFin-exchangeFin i x with Fin.inject₁ i Fin.≟ x
exchangeFin-exchangeFin i x | yes p with Fin.inject₁ i Finₚ.≟ (suc (Fin.lower₁ x (notMax i x p)))
exchangeFin-exchangeFin i .(Fin.inject₁ i) | yes refl | yes q = ⊥-elim (ℕₚ.1+n≢n (begin
  suc (Fin.toℕ i)                              ≡˘⟨ cong (suc ∘ Fin.toℕ) (Finₚ.lower₁-inject₁ i) ⟩
  suc (Fin.toℕ (Fin.lower₁ (Fin.inject₁ i) _)) ≡⟨ cong (suc ∘ Fin.toℕ) (Finₚ.lower₁-irrelevant _ _ _) ⟩
  suc (Fin.toℕ (Fin.lower₁ (Fin.inject₁ i) _)) ≡˘⟨ cong Fin.toℕ q ⟩
  Fin.toℕ (Fin.inject₁ i)                      ≡⟨ Finₚ.toℕ-inject₁ i ⟩
  Fin.toℕ i                                    ∎
  ))
exchangeFin-exchangeFin i x | yes p | no ¬q with i Finₚ.≟ Fin.lower₁ x (notMax i x p)
exchangeFin-exchangeFin i x | yes p | no ¬q | yes r = p
exchangeFin-exchangeFin i x | yes refl | no ¬q | no ¬r = ⊥-elim (¬r (begin
  i                            ≡˘⟨ Finₚ.lower₁-inject₁ i ⟩
  Fin.lower₁ (Fin.inject₁ i) _ ≡⟨ Finₚ.lower₁-irrelevant _ _ _ ⟩
  Fin.lower₁ (Fin.inject₁ i) _ ∎))
exchangeFin-exchangeFin i x | no ¬p with (suc i) Fin.≟ x
exchangeFin-exchangeFin i x | no ¬p | yes q with Fin.inject₁ i Fin.≟ Fin.inject₁ i
exchangeFin-exchangeFin i x | no ¬p | yes refl | yes refl = begin
  suc (Fin.lower₁ (Fin.inject₁ i) _)
    ≡⟨ cong suc (Finₚ.lower₁-irrelevant _ _ _) ⟩
  suc (Fin.lower₁ (Fin.inject₁ i) _)
    ≡⟨ cong suc (Finₚ.lower₁-inject₁ i) ⟩
  suc i
    ∎
exchangeFin-exchangeFin i x | no ¬p | yes q | no ¬r = ⊥-elim (¬r refl)
exchangeFin-exchangeFin i x | no ¬p | no ¬q with Fin.inject₁ i Fin.≟ x
exchangeFin-exchangeFin i x | no ¬p | no ¬q | yes r = ⊥-elim (¬p r)
exchangeFin-exchangeFin i x | no ¬p | no ¬q | no ¬r with (suc i) Fin.≟ x
exchangeFin-exchangeFin i x | no ¬p | no ¬q | no ¬r | yes s = ⊥-elim (¬q s)
exchangeFin-exchangeFin i x | no ¬p | no ¬q | no ¬r | no ¬s = refl

exchange-exchange : ∀ (i : Fin n) (P : Scoped (suc n)) → exchange i (exchange i P) ≡ P
exchange-exchange i 𝟘 = refl
exchange-exchange i (ν P) rewrite exchange-exchange (suc i) P = refl
exchange-exchange i (P ∥ Q) rewrite exchange-exchange i P | exchange-exchange i Q = refl
exchange-exchange i (x ⦅⦆ P) rewrite exchangeFin-exchangeFin i x | exchange-exchange (suc i) P = refl
exchange-exchange i (x ⟨ y ⟩ P) rewrite exchangeFin-exchangeFin i x | exchangeFin-exchangeFin i y | exchange-exchange i P = refl
