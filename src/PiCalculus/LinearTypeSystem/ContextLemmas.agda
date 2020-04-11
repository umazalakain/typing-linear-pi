open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl; subst; trans; cong)
open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to hrefl; sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)
open import Function using (_∘_)

import Data.Maybe as Maybe
import Data.Empty as Empty
import Data.Unit as Unit
import Data.Nat as ℕ
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
import Data.Fin as Fin

open Maybe using (nothing; just)
open Empty using (⊥)
open Unit using (⊤; tt)
open ℕ using (ℕ; zero; suc)
open Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₂; proj₁)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem.Quantifiers

module PiCalculus.LinearTypeSystem.ContextLemmas (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω

private
  variable
    n : ℕ
    idxs : Idxs n
    γ : PreCtx n
    idx idx' : Idx
    t : Type
    P Q : Scoped n
    i j : Fin n

only : {idxs : Idxs n} (i : Fin n) → idx ≡ Vec.lookup idxs i → Carrier idx ² → Ctx idxs
only {idxs = _ -, _} zero refl x = ε -, x
only {idxs = _ -, _} (suc i) eq x = only i eq x -, ℓ∅

channel-ℓ# : {idxs : Idxs n} (c : Channel n) → Ctx idxs
channel-ℓ# internal = ε
channel-ℓ# (external x) = only x refl ℓ#

∋-I : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : (Carrier idx) ²}
    → γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ
    → idx ≡ Vec.lookup idxs i
∋-I zero = refl
∋-I (suc x) = ∋-I x

∋-t : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : (Carrier idx) ²}
    → γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ
    → t ≡ Vec.lookup γ i
∋-t zero = refl
∋-t (suc a) = ∋-t a

∋-⊎ : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : Carrier idx ²}
    → (x : γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ)
    → Γ ≔ only {idxs = idxs} i (∋-I x) c ⊎ Ξ
∋-⊎ (zero ⦃ check ⦄) = ⊎-idˡ , proj₂ (toWitness check)
∋-⊎ (suc x) = ∋-⊎ x , ∙²-idˡ

lookup-only : {idxs : Idxs n} (i : Fin n) {c : (Carrier idx) ²}
            → (eq : idx ≡ Vec.lookup idxs i) → All.lookup i (only {idxs = idxs} i eq c) ≅ c
lookup-only {idxs = _ -, _} zero refl = hrefl
lookup-only {idxs = _ -, _} (suc i) eq = lookup-only i eq

only-∙ : {idxs : Idxs n}
       → (i : Fin n)
       → {x y z : Carrier idx ²}
       → (eq : idx ≡ Vec.lookup idxs i)
       → x ≔ y ∙² z
       → only {idxs = idxs} i eq x ≔ only {idxs = idxs} i eq y ⊎ only {idxs = idxs} i eq z
only-∙ {idxs = _ -, _} zero refl s = ⊎-idˡ , s
only-∙ {idxs = _ -, _} (suc i) eq s = only-∙ i eq s , ∙²-idˡ

only-irrel : {x : Carrier idx ²} (eqa eqb : idx ≡ Vec.lookup idxs i)
           → only {idxs = idxs} i eqa x ≡ only i eqb x
only-irrel refl refl = refl

subst-idx : ∀ {idx idx'} {eq : idx ≡ idx'} → (δ : ∀ {idx} → (Carrier idx) ²) → subst (λ i → Carrier i ²) eq δ ≡ δ
subst-idx {eq = refl} δ = refl

⊢-⊎ : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} → γ ∝ Γ ⊢ P ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
⊢-⊎ end = ε , ⊎-idˡ
⊢-⊎ (chan t m μ ⊢P) = let _ , Γ≔ = ⊢-⊎ ⊢P
                       in _ , ⊎-tail Γ≔
⊢-⊎ (recv x ⊢P) = let x≔ = ∋-⊎ x
                      _ , P≔ = ⊢-⊎ ⊢P
                   in _ , ⊎-trans x≔ (⊎-tail P≔)
⊢-⊎ (send x y ⊢P) = let x≔ = ∋-⊎ x
                        y≔ = ∋-⊎ y
                        _ , P≔ = ⊢-⊎ ⊢P
                     in _ , ⊎-trans (⊎-trans x≔ y≔) P≔
⊢-⊎ (comp ⊢P ⊢Q) = let _ , P≔ = ⊢-⊎ ⊢P
                       _ , Q≔ = ⊢-⊎ ⊢Q
                    in _ , ⊎-trans P≔ Q≔

∋-0∙ : {Γ Δ : Ctx idxs} → γ ∝ Γ [ i ]≔ t ∝ (0∙ {idx} , 0∙) ⊠ Δ → Γ ≡ Δ
∋-0∙ (zero ⦃ check ⦄) = _-,_ & refl ⊗ ∙²-unique (proj₂ (toWitness check)) ∙²-idˡ
∋-0∙ (suc x) = _-,_ & ∋-0∙ x ⊗ refl

0∙-∋ : {Γ Δ : Ctx idxs} {m : Carrier idx ²} → γ ∝ Γ [ i ]≔ t ∝ m ⊠ Δ → Γ ≡ Δ → m ≡ (0∙ , 0∙)
0∙-∋ (zero ⦃ check ⦄) eq with (toWitness check)
0∙-∋ (zero ⦃ check = check ⦄) refl | x , x≔m∙z = ∙²-uniqueˡ x≔m∙z ∙²-idˡ
0∙-∋ (suc x) eq = 0∙-∋ x (cong All.tail eq)

feedfront : {x y z a b c : Carrier idx}
          → x ≔ y ∙ z
          → a ≔ z ∙ b
          → a ≔ x ∙ c
          → b ≔ y ∙ c
feedfront xyz azb axc with ∙-assoc axc (∙-comm xyz)
feedfront xyz azb axc | [yc] , az[yc] , [yc]yc rewrite ∙-uniqueˡ (∙-comm azb) (∙-comm az[yc]) = [yc]yc

feedback : {x y z a b c : Carrier idx}
         → x ≔ y ∙ z
         → b ≔ z ∙ c
         → a ≔ x ∙ c
         → a ≔ y ∙ b
feedback xyz bzc axc with ∙-assoc axc xyz
feedback xyz bzc axc | [zc] , ay[zc] , [zc]zc rewrite ∙-unique bzc [zc]zc = ay[zc]

⊎-∋ : {idxs : Idxs n} {Γ Ξ : Ctx idxs} {x : Carrier idx ²}
    → {i : Fin n}
    → ⦃ eqt : t ≡ Vec.lookup γ i ⦄
    → ⦃ eqi : idx ≡ Vec.lookup idxs i ⦄
    → Γ ≔ only {idxs = idxs} i eqi x ⊎ Ξ
    → γ ∝ Γ [ i ]≔ t ∝ x ⊠ Ξ
⊎-∋ {γ = _ -, _} {i = zero} ⦃ refl ⦄ ⦃ refl ⦄ (Γ≔ , x≔)
  rewrite ⊎-unique Γ≔ ⊎-idˡ | ∙²-compute-unique x≔ = zero ⦃ fromWitness (_ , x≔) ⦄
⊎-∋ {γ = _ -, _} {i = suc i} (Γ≔ , x≔)
  rewrite ∙²-unique x≔ ∙²-idˡ = suc (⊎-∋ Γ≔)

mult-insert : (i : Fin (suc n)) → (Carrier idx) ² → Ctx idxs → Ctx (Vec.insert idxs i idx)
mult-insert zero xs' Γ = Γ -, xs'
mult-insert (suc i) xs' (Γ -, xs) = mult-insert i xs' Γ -, xs

mult-remove : Ctx idxs → (i : Fin (suc n)) → Ctx (Vec.remove idxs i)
mult-remove (Γ -, _) zero = Γ
mult-remove (Γ -, ys -, xs) (suc i) = mult-remove (Γ -, ys) i -, xs

mult-update : (i : Fin n) → (Carrier (Vec.lookup idxs i)) ² → Ctx idxs → Ctx idxs
mult-update zero m' (ms -, m) = ms -, m'
mult-update (suc i) m' (ms -, m) = mult-update i m' ms -, m
