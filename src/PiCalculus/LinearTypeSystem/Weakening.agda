open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function.Reasoning

import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Maybe as Maybe
import Data.Nat as Nat
import Data.Vec as Vec
import Data.Vec.Properties as Vecₚ
import Data.Bool as Bool
import Data.Fin as Fin
import Data.Vec.Relation.Unary.All as All

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
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.Weakening (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω

private
  variable
    n : ℕ
    P Q : Scoped n

insert-card : {s : Shape} {ss : Shapes n}
            → (i : Fin (suc n))
            → Card s
            → Cards ss
            → Cards (Vec.insert ss i s)
insert-card {ss = _} zero c' cs = cs , c'
insert-card {ss = _ -, _} (suc i) c' (cs , c) = insert-card i c' cs , c

insert-type : {s : Shape} {ss : Shapes n}
            → (i : Fin (suc n))
            → Type s → Types ss → Types (Vec.insert ss i s)
insert-type {ss = _} zero t' ts = ts -, t'
insert-type {ss = _ -, _} (suc i) t' (ts -, t) = insert-type i t' ts -, t

insert-mult : {s : Shape} {c : Card s} {ss : Shapes n} {cs : Cards ss}
            → (i : Fin (suc n))
            → Mult s c → Mults cs → Mults (insert-card {s = s} i c cs)
insert-mult {ss = _} zero m' ms = ms , m'
insert-mult {ss = _ -, _} (suc i) m' (ms , m) = insert-mult i m' ms , m

∋-weaken : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
         → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
         → {s' : Shape} {c' : Card s'} {t' : Type s'} {m' : Mult s' c'}
         → (i : Fin (suc n))
         → (  x : γ                 w Γ                 ∋ t' w m' ⊠ Θ)
         → Σ[ y ∈ insert-type i t γ w insert-mult i m Γ ∋ t' w m' ⊠ insert-mult i m Θ ]
           Fin.punchIn i (toFin x) ≡ toFin y
∋-weaken zero x = suc x , refl
∋-weaken (suc i) zero = zero , refl
∋-weaken (suc i) (suc x) with ∋-weaken i x
∋-weaken (suc i) (suc x) | x' , eq = suc x' , suc & eq

⊢-weaken : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Θ : Mults cs}
         → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
         → (i : Fin (suc n))
         → {P : Scoped n}
         → γ w Γ ⊢ P ⊠ Θ
         → insert-type i t γ w insert-mult i m Γ ⊢ lift i P ⊠ insert-mult i m Θ
⊢-weaken i {𝟘} end = end
⊢-weaken i {new P} (chan t m μ ⊢P) = chan t m μ (⊢-weaken (suc i) ⊢P)
⊢-weaken i {P ∥ Q} (comp ⊢P ⊢Q) = comp (⊢-weaken i ⊢P) (⊢-weaken i ⊢Q)
⊢-weaken {t = t} {m = m} i {.(toFin x) ⦅⦆ P} (recv x ⊢P)
  rewrite proj₂ (∋-weaken {t = t} {m = m} i x)
        = recv _ (⊢-weaken (suc i) ⊢P)
⊢-weaken {t = t} {m = m} i {.(toFin x) ⟨ .(toFin y) ⟩ P} (send x y ⊢P)
  rewrite proj₂ (∋-weaken {t = t} {m = m} i x)
        | proj₂ (∋-weaken {t = t} {m = m} i y)
        = send _ _ (⊢-weaken i ⊢P)
⊢-weaken i {+[] P} (base ⊢P) = base (⊢-weaken (suc i) ⊢P)
