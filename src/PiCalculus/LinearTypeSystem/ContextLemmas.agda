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
    idxs idxsᵣ : Idxs n
    γ : PreCtx n
    idx idx' : Idx
    t : Type
    P Q : Scoped n
    i j : Fin n
    Γ Δ Ξ Θ : Ctx idxs
    x x' y z : Carrier idx ²

data _≔_at_⊠_ : {idxs : Idxs n} → Ctx idxs → Carrier idx ² → Fin n → Ctx idxs → Set where
  zero : x ≔ y ∙² z
       → Γ -, x ≔ y at zero ⊠ Γ -, z
  suc : Γ ≔ x at i ⊠ Δ
      → Γ -, x' ≔ x at (suc i) ⊠ Δ -, x'

-- Contains to index equality
∋-≡Idx : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : (Carrier idx) ²}
       → γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ
       → idx ≡ Vec.lookup idxs i
∋-≡Idx zero = refl
∋-≡Idx (suc x) = ∋-≡Idx x

-- Contains to type equality
∋-≡Type : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : (Carrier idx) ²}
        → γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ
        → t ≡ Vec.lookup γ i
∋-≡Type zero = refl
∋-≡Type (suc a) = ∋-≡Type a

-- Contains to context split
∋-Only : {Γ Ξ : Ctx idxs} {x : Carrier idx ²}
       → γ ∝ Γ [ i ]≔ t ∝ x ⊠ Ξ
       → Γ ≔ x at i ⊠ Ξ
∋-Only (zero ⦃ check ⦄) = zero (proj₂ (toWitness check))
∋-Only (suc x) = suc (∋-Only x)

Only-∋ : Γ ≔ x at i ⊠ Ξ
       → Vec.lookup γ i ≡ t
       → γ ∝ Γ [ i ]≔ t ∝ x ⊠ Ξ
Only-∋ {γ = _ -, _} (zero x) refl rewrite ∙²-compute-unique x = zero ⦃ fromWitness (_ , x) ⦄
Only-∋ {γ = _ -, _} (suc only) eq = suc (Only-∋ only eq)

Only-⊎ : {Γ Ξ : Ctx idxs}
       → Γ ≔ x at i ⊠ Ξ
       → Σ[ Δ ∈ Ctx idxs ]
         (Γ ≔ Δ ⊎ Ξ × Δ ≔ x at i ⊠ ε {idxs = idxs})
Only-⊎ (zero x) = _ , (⊎-idˡ , x) , zero ∙²-idʳ
Only-⊎ (suc s) with Only-⊎ s
Only-⊎ (suc s) | _ , Γ≔ , Δ≔ = _ , (Γ≔ , ∙²-idˡ) , suc Δ≔

∋-⊎ : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {x : Carrier idx ²}
    → γ ∝ Γ [ i ]≔ t ∝ x ⊠ Ξ
    → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
∋-⊎ s = let _ , (Γ≔ , _) = Only-⊎ (∋-Only s ) in _ , Γ≔

⊎-Only : {Γ Δ Ξ : Ctx idxs}
       → Γ ≔ Δ ⊎ Ξ
       → Δ ≔ x at i ⊠ ε {idxs = idxs}
       → Γ ≔ x at i ⊠ Ξ
⊎-Only (sp , s) (zero x) rewrite ⊎-unique sp ⊎-idˡ | ∙²-unique x ∙²-idʳ = zero s
⊎-Only (sp , s) (suc only) rewrite ∙²-unique s ∙²-idˡ = suc (⊎-Only sp only)

Only-ε : Γ ≔ ℓ∅ {idx} at i ⊠ Ξ → Γ ≡ Ξ
Only-ε (zero x) rewrite ∙²-uniqueˡ (∙²-comm x) ∙²-idʳ = refl
Only-ε (suc only) rewrite Only-ε only = refl

ε-Only : Γ ≔ x at i ⊠ Γ → x ≡ ℓ∅
ε-Only (zero x) rewrite ∙²-uniqueˡ x ∙²-idˡ = refl
ε-Only (suc s) rewrite ε-Only s = refl

{-
-- lookup ∘ only = id
lookup-only : {idxs : Idxs n} (i : Fin n) {c : (Carrier idx) ²}
            → (eq : idx ≡ Vec.lookup idxs i) → All.lookup i (only {idxs = idxs} i eq c) ≅ c
lookup-only {idxs = _ -, _} zero refl = hrefl
lookup-only {idxs = _ -, _} (suc i) eq = lookup-only i eq
-}

-- Split of multiplicities to split of contexts
only-∙ : {Γ Δ Ξ : Ctx idxs}
       → Γ ≔ x at i ⊠ ε
       → Δ ≔ y at i ⊠ ε
       → Ξ ≔ z at i ⊠ ε
       → x ≔ y ∙² z
       → Γ ≔ Δ ⊎ Ξ
only-∙ (zero x) (zero y) (zero z) sp rewrite ∙²-unique x ∙²-idʳ | ∙²-unique y ∙²-idʳ | ∙²-unique z ∙²-idʳ = ⊎-idˡ , sp
only-∙ (suc Γ≔) (suc Δ≔) (suc Ξ≔) sp = only-∙ Γ≔ Δ≔ Ξ≔ sp , ∙²-idˡ

⊢-⊎ : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} → γ ∝ Γ ⊢ P ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
⊢-⊎ end = ε , ⊎-idˡ
⊢-⊎ (chan t m μ ⊢P) = let _ , Γ≔ = ⊢-⊎ ⊢P
                       in _ , ⊎-tail Γ≔
⊢-⊎ (recv x ⊢P) = let _ , x≔ = ∋-⊎ x
                      _ , P≔ = ⊢-⊎ ⊢P
                   in _ , ⊎-trans x≔ (⊎-tail P≔)
⊢-⊎ (send x y ⊢P) = let _ , x≔ = ∋-⊎ x
                        _ , y≔ = ∋-⊎ y
                        _ , P≔ = ⊢-⊎ ⊢P
                     in _ , ⊎-trans (⊎-trans x≔ y≔) P≔
⊢-⊎ (comp ⊢P ⊢Q) = let _ , P≔ = ⊢-⊎ ⊢P
                       _ , Q≔ = ⊢-⊎ ⊢Q
                    in _ , ⊎-trans P≔ Q≔

feedfront : {x y z a b c : Ctx idxs}
        → x ≔ y ⊎ z
        → a ≔ z ⊎ b
        → a ≔ x ⊎ c
        → b ≔ y ⊎ c
feedfront xyz azb axc with ⊎-assoc axc (⊎-comm xyz)
feedfront xyz azb axc | [yc] , az[yc] , [yc]yc rewrite ⊎-uniqueˡ (⊎-comm azb) (⊎-comm az[yc]) = [yc]yc

feedback : {x y z a b c : Ctx idxs}
       → x ≔ y ⊎ z
       → b ≔ z ⊎ c
       → a ≔ x ⊎ c
       → a ≔ y ⊎ b
feedback xyz bzc axc with ⊎-assoc axc xyz
feedback xyz bzc axc | [zc] , ay[zc] , [zc]zc rewrite ⊎-unique bzc [zc]zc = ay[zc]

mult-insert : (i : Fin (suc n)) → (Carrier idx) ² → Ctx idxs → Ctx (Vec.insert idxs i idx)
mult-insert zero xs' Γ = Γ -, xs'
mult-insert (suc i) xs' (Γ -, xs) = mult-insert i xs' Γ -, xs

mult-remove : Ctx idxs → (i : Fin (suc n)) → Ctx (Vec.remove idxs i)
mult-remove (Γ -, _) zero = Γ
mult-remove (Γ -, ys -, xs) (suc i) = mult-remove (Γ -, ys) i -, xs

mult-update : (i : Fin n) → (Carrier (Vec.lookup idxs i)) ² → Ctx idxs → Ctx idxs
mult-update zero m' (ms -, m) = ms -, m'
mult-update (suc i) m' (ms -, m) = mult-update i m' ms -, m
