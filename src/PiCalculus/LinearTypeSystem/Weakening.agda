{-# OPTIONS --safe #-} --without-K #-}

import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Fin as Fin
import Data.Vec.Relation.Unary.All as All

open Nat using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (_,_)

import PiCalculus.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Algebras

module PiCalculus.LinearTypeSystem.Weakening (Ω : Algebras) where
open Algebras Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem Ω

private
  variable
    n : ℕ
    i j : Fin n
    idx idx' : Idx
    idxs : Idxs n
    P Q : Scoped n

∋-weaken : {γ : PreCtx n} {Γ Θ : Ctx idxs} {t t' : Type} {xs : Usage idx ²} {xs' : Usage idx' ²}
         → (j : Fin (suc n))
         → γ                ； Γ                 ∋[ i               ] t' ； xs' ▹ Θ
         → Vec.insert γ j t ； ctx-insert j xs Γ ∋[ Fin.punchIn j i ] t' ； xs' ▹ ctx-insert j xs Θ
∋-weaken zero x = there x
∋-weaken (suc i) (zero , zero xyz) = zero , zero xyz
∋-weaken (suc i) (suc t , suc x) = there (∋-weaken i (t , x))

⊢-weaken : {P : Scoped n} {γ : PreCtx n} {Γ Θ : Ctx idxs} {t : Type} {xs : Usage idx ²}
         → (j : Fin (suc n))
         → γ ； Γ ⊢ P ▹ Θ
         → Vec.insert γ j t ； ctx-insert j xs Γ ⊢ lift j P ▹ ctx-insert j xs Θ
⊢-weaken j 𝟘 = 𝟘
⊢-weaken j (ν t m μ ⊢P) = ν t m μ (⊢-weaken (suc j) ⊢P)
⊢-weaken j (⊢P ∥ ⊢Q) = ⊢-weaken j ⊢P ∥ ⊢-weaken j ⊢Q
⊢-weaken j (x ⦅⦆ ⊢P) = ∋-weaken j x ⦅⦆ ⊢-weaken (suc j) ⊢P
⊢-weaken j (x ⟨ y ⟩ ⊢P) = ∋-weaken j x ⟨ ∋-weaken j y ⟩ ⊢-weaken j ⊢P
