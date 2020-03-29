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

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Weakening (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem Ω

private
  variable
    n : ℕ
    i j : Fin n
    idx idx' : Idx
    idxs : Idxs n
    P Q : Scoped n

∋-weaken : {γ : PreCtx n} {Γ Θ : Ctx idxs} {t t' : Type} {xs : Carrier idx ²} {xs' : Carrier idx' ²}
         → (j : Fin (suc n))
         → γ                ∝ Γ                  [ i               ]≔ t' ∝ xs' ⊠ Θ
         → Vec.insert γ j t ∝ mult-insert j xs Γ [ Fin.punchIn j i ]≔ t' ∝ xs' ⊠ mult-insert j xs Θ
∋-weaken zero x = suc x
∋-weaken (suc i) zero = zero
∋-weaken (suc i) (suc x) = suc (∋-weaken i x)

⊢-weaken : {γ : PreCtx n} {Γ Θ : Ctx idxs} {t : Type} {xs : Carrier idx ²}
         → (j : Fin (suc n))
         → {P : Scoped n}
         → γ ∝ Γ ⊢ P ⊠ Θ
         → Vec.insert γ j t ∝ mult-insert j xs Γ ⊢ lift j P ⊠ mult-insert j xs Θ
⊢-weaken j end = end
⊢-weaken j (chan t m μ ⊢P) = chan t m μ (⊢-weaken (suc j) ⊢P)
⊢-weaken j (comp ⊢P ⊢Q) = comp (⊢-weaken j ⊢P) (⊢-weaken j ⊢Q)
⊢-weaken j (recv x ⊢P) = recv (∋-weaken j x) (⊢-weaken (suc j) ⊢P)
⊢-weaken j (send x y ⊢P) = send (∋-weaken j x) (∋-weaken j y) (⊢-weaken j ⊢P)
