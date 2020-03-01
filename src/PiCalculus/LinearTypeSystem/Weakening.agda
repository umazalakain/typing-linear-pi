open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function.Reasoning

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
open Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.Quantifiers

module PiCalculus.LinearTypeSystem.Weakening (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem Ω

private
  variable
    n : ℕ
    i i' : I
    P Q : Scoped n

insert-mult : {γ : PreCtx n} (i : Fin (suc n)) {t' : Type}
            → Usage (i' , t') → Ctx γ → Ctx (Vec.insert γ i (i' , t'))
insert-mult zero xs' Γ = Γ -, xs'
insert-mult (suc i) xs' (Γ -, xs) = insert-mult i xs' Γ -, xs

∋-weaken : {γ : PreCtx n} {Γ Θ : Ctx γ} {t t' : Type} {xs : Usage (i , t)} {xs' : Usage (i' , t')}
         → (f : Fin (suc n))
         → (  x : γ                      w Γ                  ∋ t' w xs' ⊠ Θ)
         → Σ[ y ∈ Vec.insert γ f (i , t) w insert-mult f xs Γ ∋ t' w xs' ⊠ insert-mult f xs Θ ]
           Fin.punchIn f (toFin x) ≡ toFin y
∋-weaken zero x = suc x , refl
∋-weaken (suc i) zero = zero , refl
∋-weaken (suc i) (suc x) with ∋-weaken i x
∋-weaken (suc i) (suc x) | x' , eq = suc x' , suc & eq

⊢-weaken : {γ : PreCtx n} {Γ Θ : Ctx γ} {t : Type} {xs : Usage (i , t)}
         → (f : Fin (suc n))
         → {P : Scoped n}
         → γ w Γ ⊢ P ⊠ Θ
         → Vec.insert γ f (i , t) w insert-mult f xs Γ ⊢ lift f P ⊠ insert-mult f xs Θ
⊢-weaken i {𝟘} end = end
⊢-weaken i {new P} (chan t m μ ⊢P) = chan t m μ (⊢-weaken (suc i) ⊢P)
⊢-weaken i {P ∥ Q} (comp ⊢P ⊢Q) = comp (⊢-weaken i ⊢P) (⊢-weaken i ⊢Q)
⊢-weaken {t = t} {xs = xs} i {.(toFin x) ⦅⦆ P} (recv x ⊢P)
  rewrite proj₂ (∋-weaken {t = t} {xs = xs} i x)
        = recv _ (⊢-weaken (suc i) ⊢P)
⊢-weaken {t = t} {xs = xs} i {.(toFin x) ⟨ .(toFin y) ⟩ P} (send x y ⊢P)
  rewrite proj₂ (∋-weaken {t = t} {xs = xs} i x)
        | proj₂ (∋-weaken {t = t} {xs = xs} i y)
        = send _ _ (⊢-weaken i ⊢P)
⊢-weaken i {+[] P} (base ⊢P) = base (⊢-weaken (suc i) ⊢P)
