open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂)
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
open Syntax
open Scoped
open import PiCalculus.Semantics
open import PiCalculus.Function

module PiCalculus.Semantics.Properties where
private
  variable
    n : ℕ
    i j : Fin n
    P : Scoped n

lift-lower : (i : Fin (suc n)) (P : Scoped (suc n)) (uP : Unused i P)
           → lift i (lower i P uP) ≡ P
lift-lower i 𝟘 uP = refl
lift-lower i (new P) uP
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

swapFin-suc : (i : Fin n) (x : Fin (suc n)) → suc (swapFin i x) ≡ swapFin (suc i) (suc x)
swapFin-suc i x with Fin.inject₁ i Finₚ.≟ x
swapFin-suc i .(Fin.inject₁ i) | yes refl = suc & (suc & Finₚ.lower₁-irrelevant _ _ _)
swapFin-suc i x | no ¬p with (suc i) Fin.≟ x
swapFin-suc i x | no ¬p | yes q = refl
swapFin-suc i x | no ¬p | no ¬q = refl

swapFin-swapFin : ∀ (i : Fin n) (x : Fin (suc n)) → swapFin i (swapFin i x) ≡ x
swapFin-swapFin i x with Fin.inject₁ i Fin.≟ x
swapFin-swapFin i x | yes p with Fin.inject₁ i Finₚ.≟ (suc (Fin.lower₁ x (notMax i x p)))
swapFin-swapFin i .(Fin.inject₁ i) | yes refl | yes q = ⊥-elim (ℕₚ.1+n≢n (begin
  suc (Fin.toℕ i)                              ≡˘⟨ suc & (Fin.toℕ & Finₚ.lower₁-inject₁ i) ⟩
  suc (Fin.toℕ (Fin.lower₁ (Fin.inject₁ i) _)) ≡⟨ suc & (Fin.toℕ & Finₚ.lower₁-irrelevant _ _ _) ⟩
  suc (Fin.toℕ (Fin.lower₁ (Fin.inject₁ i) _)) ≡˘⟨ Fin.toℕ & q ⟩
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
    ≡⟨ suc & Finₚ.lower₁-irrelevant _ _ _ ⟩
  suc (Fin.lower₁ (Fin.inject₁ i) _)
    ≡⟨ suc & (Finₚ.lower₁-inject₁ i) ⟩
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
swap-swap i (new P) rewrite swap-swap (suc i) P = refl
swap-swap i (P ∥ Q) rewrite swap-swap i P | swap-swap i Q = refl
swap-swap i (x ⦅⦆ P) rewrite swapFin-swapFin i x | swap-swap (suc i) P = refl
swap-swap i (x ⟨ y ⟩ P) rewrite swapFin-swapFin i x | swapFin-swapFin i y | swap-swap i P = refl
