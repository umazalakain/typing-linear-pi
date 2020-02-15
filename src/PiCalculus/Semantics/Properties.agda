open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)

import Data.Nat as ℕ
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
lift-lower i (+[] P) uP
  rewrite lift-lower (suc i) P uP = refl

{-
swap-swap : ∀ (i j : Fin n) (P : Scoped n) → swap i j (swap i j P) ≡ P
swap-swap i j 𝟘 = refl
swap-swap i j (new P) = new_ & swap-swap _ _ P
swap-swap i j (P ∥ Q) = _∥_ & swap-swap _ _ P ⊗ swap-swap _ _ Q
swap-swap i j (x ⦅⦆ P) with i Finₚ.≟ x
swap-swap i j (.i ⦅⦆ P) | yes refl with i Finₚ.≟ j
swap-swap i .i (.i ⦅⦆ P) | yes refl | yes refl = _⦅⦆_ & refl ⊗ swap-swap _ _ P
swap-swap i j (.i ⦅⦆ P) | yes refl | no ¬p with j Finₚ.≟ j
swap-swap i j (.i ⦅⦆ P) | yes refl | no ¬p | yes refl = _⦅⦆_ & refl ⊗ swap-swap _ _ P
swap-swap i j (.i ⦅⦆ P) | yes refl | no ¬p | no ¬q = ⊥-elim (¬q refl)
swap-swap i j (x ⦅⦆ P) | no ¬p with j Finₚ.≟ x
swap-swap i .x (x ⦅⦆ P) | no ¬p | yes refl with i Finₚ.≟ i
swap-swap i .x (x ⦅⦆ P) | no ¬p | yes refl | yes refl = _⦅⦆_ & refl ⊗ swap-swap _ _ P
swap-swap i .x (x ⦅⦆ P) | no ¬p | yes refl | no ¬q = ⊥-elim (¬q refl)
swap-swap i j (x ⦅⦆ P) | no ¬p | no ¬q with i Finₚ.≟ x
swap-swap .x j (x ⦅⦆ P) | no ¬p | no ¬q | yes refl = ⊥-elim (¬p refl)
swap-swap i j (x ⦅⦆ P) | no ¬p | no ¬q | no ¬p₁ with j Finₚ.≟ x
swap-swap i .x (x ⦅⦆ P) | no ¬p | no ¬q | no ¬p₁ | yes refl = ⊥-elim (¬q refl)
swap-swap i j (x ⦅⦆ P) | no ¬p | no ¬q | no ¬p₁ | no ¬p₂ = _⦅⦆_ & refl ⊗ swap-swap _ _ P
swap-swap i j (x ⟨ y ⟩ P) = {!!}
swap-swap i j (+[] P) = {!!}
-}
