{-# OPTIONS --safe #-} -- --without-K #-}

open import Function using (_∘_; id)
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
    n m l : ℕ
    i j : Fin n
    P : Scoped n


lift-lower : (i : Fin (suc n)) (P : Scoped (suc n)) (uP : Unused i P)
           → |> suc (lower i P uP) ≡ P
lift-lower {n = zero} zero 𝟘 uP = refl
lift-lower {n = zero} zero (ν P) uP rewrite lift-lower (suc zero) P uP = {!!}
lift-lower {n = zero} zero (P ∥ P₁) uP = {!!}
lift-lower {n = zero} zero (x ⦅⦆ P) uP = {!!}
lift-lower {n = zero} zero (x ⟨ x₁ ⟩ P) uP = {!!}
lift-lower {n = suc n} i 𝟘 uP = refl
lift-lower {n = suc n} i (ν P) uP
  rewrite lift-lower (suc i) P uP = {!refl!}
lift-lower {n = suc n} i (P ∥ Q) (uP , uQ)
  rewrite lift-lower i P uP
  | lift-lower i Q uQ = {!!}
lift-lower {n = suc n} i (x ⦅⦆ P) (i≢x , uP)
  rewrite lift-lower (suc i) P uP
  | Finₚ.punchIn-punchOut i≢x = {!!}
lift-lower {n = suc n} i (x ⟨ y ⟩ P) (i≢x , i≢y , uP)
  rewrite lift-lower i P uP
  | Finₚ.punchIn-punchOut i≢x
  | Finₚ.punchIn-punchOut i≢y = {!!}

exchangeFin-exchangeFin : ∀ (i : Fin n) (x : Fin (suc n)) → exchangeFin i (exchangeFin i x) ≡ x
exchangeFin-exchangeFin zero zero = refl
exchangeFin-exchangeFin zero (suc zero) = refl
exchangeFin-exchangeFin zero (suc (suc x)) = refl
exchangeFin-exchangeFin (suc i) zero = refl
exchangeFin-exchangeFin (suc i) (suc x) = cong suc (exchangeFin-exchangeFin i x)

suc-|>-cong : (g f : Fin n → Fin m) → (∀ x → f x ≡ g x) → (∀ x → suc-|> f x ≡ suc-|> g x)
suc-|>-cong g f eq zero = refl
suc-|>-cong g f eq (suc x) = cong suc (eq x)

suc-|>-comp : (g : Fin n → Fin m) (f : Fin m → Fin l) (x : Fin (suc n)) → suc-|> (f ∘ g) x ≡ (suc-|> f ∘ suc-|> g) x
suc-|>-comp g f zero = refl
suc-|>-comp g f (suc x) = refl

suc-|>-id : (x : Fin (suc n)) → (suc-|> id) x ≡ x
suc-|>-id zero = refl
suc-|>-id (suc x) = refl

|>-ext : (g f : Fin n → Fin m) → (∀ x → f x ≡ g x) → (∀ P → |> f P ≡ |> g P)
|>-ext g f eq 𝟘 = refl
|>-ext g f eq (ν P) = cong (λ ● → ν ●) (|>-ext (suc-|> g) (suc-|> f) (suc-|>-cong g f eq) P)
|>-ext g f eq (P ∥ Q) = cong₂ _∥_ (|>-ext g f eq P) (|>-ext g f eq Q)
|>-ext g f eq (x ⦅⦆ P) rewrite eq x = cong (_ ⦅⦆_) (|>-ext (suc-|> g) (suc-|> f) (suc-|>-cong g f eq) P)
|>-ext g f eq (x ⟨ y ⟩ P) rewrite eq x | eq y = cong (_ ⟨ _ ⟩_) (|>-ext g f eq P)

|>-id : (P : Scoped n) → |> id P ≡ P
|>-id 𝟘 = refl
|>-id (ν P) rewrite |>-ext _ _ suc-|>-id P = cong (λ ● → ν ●) (|>-id P)
|>-id (P ∥ Q) = cong₂ _∥_ (|>-id P) (|>-id Q)
|>-id (x ⦅⦆ P) rewrite |>-ext _ _ suc-|>-id P = cong (_ ⦅⦆_) (|>-id P)
|>-id (x ⟨ y ⟩ P) = cong (_ ⟨ _ ⟩_) (|>-id P)

|>-comp : (g : Fin n → Fin m) (f : Fin m → Fin l) (P : Scoped n) → |> f (|> g P) ≡ |> (f ∘ g) P
|>-comp g f 𝟘 = refl
|>-comp g f (ν P)
  rewrite |>-ext _ _ (suc-|>-comp g f) P = cong (λ ● → ν ●) (|>-comp _ _ P)
|>-comp g f (P ∥ Q) = cong₂ _∥_ (|>-comp g f P) (|>-comp g f Q)
|>-comp g f (x ⦅⦆ P)
  rewrite |>-ext _ _ (suc-|>-comp g f) P = cong (_ ⦅⦆_) (|>-comp _ _ P)
|>-comp g f (x ⟨ y ⟩ P) = cong (_ ⟨ _ ⟩_) (|>-comp _ _ P)

exchange-exchange : ∀ (i : Fin n) (P : Scoped (suc n)) → |> (exchangeFin  i) (|> (exchangeFin i) P) ≡ P
exchange-exchange i P
  rewrite |>-comp (exchangeFin i) (exchangeFin i) P
  | |>-ext _ _ (exchangeFin-exchangeFin i) P = |>-id P
