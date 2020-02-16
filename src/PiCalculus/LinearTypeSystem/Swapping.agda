open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function.Reasoning
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

import Data.Empty as Empty
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Maybe as Maybe
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Bool as Bool
import Data.Fin as Fin
import Data.Fin.Properties as Finₚ
import Data.Vec.Relation.Unary.All as All

open Empty using (⊥-elim)
open Unit using (⊤; tt)
open Nat using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.OmegaNat
open import PiCalculus.LinearTypeSystem.ContextLemmas

module PiCalculus.LinearTypeSystem.Swapping where

private
  variable
    n : ℕ
    P Q : Scoped n

get-shape : Shapes n → Fin n → Shape
get-shape = Vec.lookup

get-type : {ss : Shapes n} → Types ss → (i : Fin n) → Type (get-shape ss i)
get-type {ss = _ -, _} (ts -, t) zero = t
get-type {ss = _ -, _} (ts -, t) (suc i) = get-type ts i

get-card : {ss : Shapes n} → Cards ss → (i : Fin n) → Card (get-shape ss i)
get-card {ss = _ -, _} (cs , c) zero = c
get-card {ss = _ -, _} (cs , c) (suc i) = get-card cs i

get-mult : {ss : Shapes n} {cs : Cards ss} → Mults cs → (i : Fin n)
         → Mult (get-shape ss i) (get-card cs i)
get-mult {ss = _ -, _} (ms , m) zero = m
get-mult {ss = _ -, _} (ms , m) (suc i) = get-mult ms i


∋-unused : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
         → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
         → (i : Fin n)
         → (x : γ w Γ ∋ t w m ⊠ Θ)
         → i ≢ toFin x
         → get-mult Γ i ≡ get-mult Θ i
∋-unused zero zero i≢x = ⊥-elim (i≢x refl)
∋-unused zero (suc x) i≢x = refl
∋-unused (suc i) zero i≢x = refl
∋-unused (suc i) (suc x) i≢x = ∋-unused i x (i≢x ∘ cong suc)

⊢-unused : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
         → (i : Fin n)
         → Unused i P
         → γ w Γ ⊢ P ⊠ Θ
         → get-mult Γ i ≡ get-mult Θ i
⊢-unused i uP end = refl
⊢-unused i uP (base ⊢P) = ⊢-unused (suc i) uP ⊢P
⊢-unused i uP (chan t m μ ⊢P) = ⊢-unused (suc i) uP ⊢P
⊢-unused i (i≢x , uP) (recv x ⊢P) = trans
  (∋-unused i x i≢x)
  (⊢-unused (suc i) uP ⊢P)
⊢-unused i (i≢x , i≢y , uP) (send x y ⊢P) = trans (trans
  (∋-unused i x i≢x)
  (∋-unused i y i≢y))
  (⊢-unused i uP ⊢P)
⊢-unused i (uP , uQ) (comp ⊢P ⊢Q) = trans
  (⊢-unused i uP ⊢P)
  (⊢-unused i uQ ⊢Q)

update-shape : Fin n → Shape → Shapes n → Shapes n
update-shape i s = Vec.updateAt i λ _ → s

update-type : {s : Shape} {ss : Shapes n}
                → (i : Fin n)
                → Type s
                → Types ss
                → Types (update-shape i s ss)
update-type {ss = _ -, _} zero t' (ts -, t) = ts -, t'
update-type {ss = _ -, _} (suc i) t' (ts -, t) = update-type i t' ts -, t

update-card : {s : Shape} {ss : Shapes n}
                → (i : Fin n)
                → Card s
                → Cards ss
                → Cards (update-shape i s ss)
update-card {ss = _ -, _} zero c' (cs , c) = cs , c'
update-card {ss = _ -, _} (suc i) c' (cs , c) = update-card i c' cs , c

update-mult : {s : Shape} {ss : Shapes n} {c : Card s} {cs : Cards ss}
                → (i : Fin n)
                → Mult s c
                → Mults cs
                → Mults (update-card {s = s} i c cs)
update-mult {ss = _ -, _} zero m' (ms , m) = ms , m'
update-mult {ss = _ -, _} (suc i) m' (ms , m) = update-mult i m' ms , m

subst-shape : Fin n → Fin n → Shapes n → Shapes n
subst-shape i j ss = update-shape i (get-shape ss j) ss

subst-type : {ss : Shapes n} (i j : Fin n) → Types ss → Types (subst-shape i j ss)
subst-type i j ts = update-type i (get-type ts j) ts

subst-card : {ss : Shapes n} (i j : Fin n) → Cards ss → Cards (subst-shape i j ss)
subst-card i j cs = update-card i (get-card cs j) cs

subst-mult : {ss : Shapes n} {cs : Cards ss} (i j : Fin n) → Mults cs → Mults (subst-card i j cs)
subst-mult i j ms = update-mult i (get-mult ms j) ms

swap-shape : Fin n → Fin n → Shapes n → Shapes n
swap-shape i j ss = subst-shape i j (subst-shape j i ss)

swap-type : {ss : Shapes n} → (i j : Fin n) → Types ss → Types (swap-shape i j ss)
swap-type i j ts = subst-type i j (subst-type j i ts)

swap-card : {ss : Shapes n} → (i j : Fin n) → Cards ss → Cards (swap-shape i j ss)
swap-card i j cs = subst-card i j (subst-card j i cs)

swap-mult : {ss : Shapes n} {cs : Cards ss} → (i j : Fin n) → Mults cs → Mults (swap-card i j cs)
swap-mult i j ms = subst-mult i j (subst-mult j i ms)

{-
∋-subst : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
        → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
        → (i j : Fin n)
        → (x : γ w Γ ∋ t w m ⊠ Θ)
        → Σ[ y ∈ subst-type i j γ w subst-mult i j Γ ∋ t w m ⊠ subst-mult i j Θ ]
          substFin j i (toFin x) ≡ toFin y
∋-subst zero zero zero = zero , refl
∋-subst {n = suc (suc n)} zero (suc j) zero with ∋-subst {n = suc n} zero j zero
∋-subst {suc (suc n)} zero (suc j) zero | fst , snd = suc {!fst!} , {!!}
∋-subst zero j (suc x) = {!suc ?!} , {!!}
∋-subst (suc i) j zero = {!!} , {!!}
∋-subst (suc i) j (suc x) = {!!}

∋-swap : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
       → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
       → (i j : Fin n)
       → (x : γ w Γ ∋ t w m ⊠ Θ)
       → Σ[ y ∈ swap-type i j γ w swap-mult i j Γ ∋ t w m ⊠ swap-mult i j Θ ]
         swapFin i j (toFin x) ≡ toFin y
∋-swap i j x = {!!}

⊢-swap : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
       → (i j : Fin n)
       → γ w Γ ⊢ P ⊠ Θ
       → swap-type i j γ w swap-mult i j Γ ⊢ swap i j P ⊠ swap-mult i j Θ
⊢-swap i j end = end
⊢-swap i j (base ⊢P) = base (⊢-swap (suc i) (suc j) ⊢P)
⊢-swap i j (chan t m μ ⊢P) = chan t m μ (⊢-swap (suc i) (suc j) ⊢P)
⊢-swap i j (recv x ⊢P) rewrite proj₂ (∋-swap i j x) = recv _ (⊢-swap (suc i) (suc j) ⊢P)
⊢-swap i j (send x y ⊢P) rewrite proj₂ (∋-swap i j x) | proj₂ (∋-swap i j y) = send _ _ (⊢-swap i j ⊢P)
⊢-swap i j (comp ⊢P ⊢Q) = comp (⊢-swap i j ⊢P) (⊢-swap i j ⊢Q)
-}
