import Data.Maybe as Maybe
import Data.Nat as Nat
import Data.Bool as Bool
import Data.Fin as Fin
import Data.Product as Product

open Nat using (ℕ; zero; suc)
open Fin using (Fin ; zero ; suc)
open Maybe using (nothing; just)
open Product using (_,_)

open import PiCalculus.Syntax
open Scoped
open Syntax
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.OmegaNat
open import PiCalculus.LinearTypeSystem.ContextLemmas
open import PiCalculus.LinearTypeSystem.SubjectCongruence

module PiCalculus.LinearTypeSystem.SubjectReduction where

maybe-consume : {n : ℕ} {ss : Shapes n} {cs : Cards ss} → Mults cs → Channel n → Mults cs
maybe-consume Γ nothing = Γ
maybe-consume {ss = _ -, _} (Γ , m) (just zero) = Γ , replicate ω0
maybe-consume {ss = _ -, _} (Γ , m) (just (suc i)) = maybe-consume Γ (just i) , m

SubjectReduction : Set
SubjectReduction = {n : ℕ} {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
                   {c : Channel n} {P Q : Scoped n}
                 → P =[ c ]⇒ Q
                 → γ w Γ                 ⊢ P ⊠ Δ
                 → γ w maybe-consume Γ c ⊢ Q ⊠ maybe-consume Δ c

private
  variable
    n : ℕ
    P Q : Scoped n

subject-reduction : SubjectReduction
subject-reduction comm (comp (recv x ⊢P) ⊢Q) = {!⊢Q!}
subject-reduction {c = nothing} (par P⇒P') (comp ⊢P ⊢Q) = comp (subject-reduction P⇒P' ⊢P) ⊢Q
subject-reduction {c = just i} (par P⇒P') (comp ⊢P ⊢Q) = {!!}
subject-reduction (res {c = nothing} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ μ (subject-reduction P⇒Q ⊢P)
subject-reduction (res {c = just zero} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ ω0 (subject-reduction P⇒Q ⊢P)
subject-reduction (res {c = just (suc i)} P⇒Q) (chan γ δ μ ⊢P) = chan γ δ μ (subject-reduction P⇒Q ⊢P)
subject-reduction (base {c = nothing} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (base {c = just zero} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (base {c = just (suc x)} P⇒Q) (base ⊢P) = base (subject-reduction P⇒Q ⊢P)
subject-reduction (struct P≅P' P'⇒Q) ⊢P = subject-reduction P'⇒Q (subject-cong P≅P' ⊢P)
