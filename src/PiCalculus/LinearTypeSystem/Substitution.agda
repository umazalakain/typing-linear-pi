open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary.Decidable using (toWitness; fromWitness)
open import Relation.Nullary using (yes; no)
open import Function.Reasoning
open import Function using (_∘_)

import Data.Empty as Empty
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Nat.Base as Nat
import Data.Vec.Base as Vec
import Data.Vec.Properties as Vecₚ
import Data.Fin.Base as Fin
import Data.Vec.Relation.Unary.All as All

open Empty using (⊥-elim)
open Unit using (tt)
open Nat using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Substitution (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    i j : Fin n
    t : Type
    γ : PreCtx n
    idx : I
    idxs : Vec I n
    x : Cs idx
    Γ Δ Δ' Θ : Ctx idxs
    P : Scoped n

data _w_[_/_]≔_ : PreCtx n → Ctx idxs → Fin n → Fin n → Ctx idxs → Set where
  zero : (i : γ w Γ ∋ t w x ⊠ Δ)
       → γ -, t w Γ -, 0∙ [ suc (toFin i) / zero  ]≔ Δ -, x
  suc  : γ w Γ [ i / j ]≔ Δ
       → γ -, t w Γ -, x  [ suc i         / suc j ]≔ Δ -, x

{-
      Γ -, x ⊢ P                  ⊠ Δ  -, 0∙
  ==> Γ -, x ⊢ [ suc i / zero ] P ⊠ Δ' -, x
      where Δ ≔ Δ' ⊎ x at i

  If P is 𝟘
      Γ -, x ⊢ 𝟘 ⊠ Γ  -, 0∙  -- empty
  ==> Γ -, x ⊢ 𝟘 ⊠ Γ' -, x
      where Γ ≔ Γ' ⊎ x at i

  Relation between Δ -, 0∙ and Δ' -, x:

-}

postulate
  ∋-0∙ : {γ : PreCtx n} {idxs : Vec I n} {Γ : Ctx idxs} → γ w Γ ∋ t w x ⊠ Γ → x ≡ 0∙

postulate
  ⊢-subst : {γ : PreCtx n} {idxs : Vec I n} {Γ Δ Θ : Ctx idxs} {i j : Fin n}
          → All.lookup j Γ ≢ All.lookup j Δ
          → γ w Γ ⊢           P ⊠ Δ
          → γ w Δ   [ i / j ]≔    Θ
          → γ w Γ ⊢ [ i / j ] P ⊠ Θ
          {-
⊢-subst neq end Δ~Θ = ⊥-elim (neq refl)
⊢-subst neq (chan t m μ ⊢P) Δ~Θ = chan t m μ (⊢-subst neq ⊢P (suc Δ~Θ))
⊢-subst neq (recv x ⊢P) Δ~Θ = {!!}
⊢-subst neq (send x y ⊢P) Δ~Θ = {!!}
⊢-subst neq (comp ⊢P ⊢Q) Δ~Θ = comp (⊢-subst {!!} ⊢P {!!}) {!!}

-}
