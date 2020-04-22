open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl; subst; trans; cong)
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
open Empty using (⊥; ⊥-elim)
open Unit using (⊤; tt)
open ℕ using (ℕ; zero; suc)
open Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₂; proj₁)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Relation.Binary.PropositionalEquality.≡-Reasoning

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

Only-≡Idx : {Γ : Ctx idxs} {x : Carrier idx ²} → Γ ≔ x at i ⊠ Δ → Vec.lookup idxs i ≡ idx
Only-≡Idx (zero x) = refl
Only-≡Idx (suc s) rewrite Only-≡Idx s = refl

-- TODO: DEPRECATED
-- Contains to index equality
∋-≡Idx : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : (Carrier idx) ²}
       → γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ
       → Vec.lookup idxs i ≡ idx
∋-≡Idx zero = refl
∋-≡Idx (suc x) = ∋-≡Idx x

-- Contains to type equality
∋-≡Type : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs} {c : (Carrier idx) ²}
        → γ ∝ Γ [ i ]≔ t ∝ c ⊠ Ξ
        → Vec.lookup γ i ≡ t
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

Only-ℓ∅-≡ : Γ ≔ ℓ∅ {idx} at i ⊠ Ξ → Γ ≡ Ξ
Only-ℓ∅-≡ (zero x) rewrite ∙²-uniqueˡ (∙²-comm x) ∙²-idʳ = refl
Only-ℓ∅-≡ (suc only) rewrite Only-ℓ∅-≡ only = refl

Only-≡ℓ∅ : Γ ≔ x at i ⊠ Γ → x ≡ ℓ∅
Only-≡ℓ∅ (zero x) rewrite ∙²-uniqueˡ x ∙²-idˡ = refl
Only-≡ℓ∅ (suc s) rewrite Only-≡ℓ∅ s = refl

Only-ℓ∅ : {idxs : Idxs n} {Γ : Ctx idxs} {i : Fin n} {idx : Idx}→ Vec.lookup idxs i ≡ idx → Γ ≔ ℓ∅ {idx} at i ⊠ Γ
Only-ℓ∅ {Γ = _ -, _} {i = zero} refl = zero ∙²-idˡ
Only-ℓ∅ {Γ = _ -, _} {i = suc i} eq = suc (Only-ℓ∅ eq)

-- TODO: deprecate, convert to context first
Only-uniqueʳ : Γ ≔ x at i ⊠ Δ → Γ ≔ x at i ⊠ Ξ → Δ ≡ Ξ
Only-uniqueʳ (zero a) (zero b) rewrite ∙²-uniqueˡ (∙²-comm a) (∙²-comm b) = refl
Only-uniqueʳ (suc a) (suc b) rewrite Only-uniqueʳ a b = refl

-- TODO: deprecate, convert to context first
Only-uniqueˡ : Γ ≔ x at i ⊠ Δ → Ξ ≔ x at i ⊠ Δ → Γ ≡ Ξ
Only-uniqueˡ (zero a) (zero b) rewrite ∙²-unique a b = refl
Only-uniqueˡ (suc a) (suc b) rewrite Only-uniqueˡ a b = refl

Only-lookup-≡ : Γ ≔ x at i ⊠ Δ → All.lookup i Γ ≔ x ∙² All.lookup i Δ
Only-lookup-≡ {i = zero} (zero x) = x
Only-lookup-≡ {i = suc i} (suc s) = Only-lookup-≡ s

Only-idʳ : {x : Carrier idx ²} → Vec.lookup idxs i ≡ idx → Σ[ Γ ∈ Ctx idxs ] (Γ ≔ x at i ⊠ ε {idxs = idxs})
Only-idʳ {idxs = idxs -, _} {i = zero} refl = (_ -, _) , zero ∙²-idʳ
Only-idʳ {idxs = idxs -, _} {i = suc i} eq with Only-idʳ {idxs = idxs} {i = i} eq
Only-idʳ {idxs = idxs -, _} {i = suc i} eq | _ , Γ≔ = _ , suc Γ≔

Only-lookup-≢ : Γ ≔ x at i ⊠ Δ → ∀ j → i ≢ j → All.lookup j Γ ≡ All.lookup j Δ
Only-lookup-≢ (zero x) zero i≢j = ⊥-elim (i≢j refl)
Only-lookup-≢ (suc xati) zero i≢j = refl
Only-lookup-≢ (zero x) (suc j) i≢j = refl
Only-lookup-≢ (suc xati) (suc j) i≢j = Only-lookup-≢ xati j (i≢j ∘ cong suc)

lookup-ε : ∀ i → All.lookup i (ε {idxs = idxs}) ≡ ℓ∅
lookup-ε {idxs = _ -, _} zero = refl
lookup-ε {idxs = _ -, _} (suc i) = lookup-ε i

-- TODO: CHANGE NAME
-- Split of multiplicities to split of contexts
only-∙ : {Γ Δ Ξ : Ctx idxs}
       → Γ ≔ x at i ⊠ ε
       → Δ ≔ y at i ⊠ ε
       → Ξ ≔ z at i ⊠ ε
       → x ≔ y ∙² z
       → Γ ≔ Δ ⊎ Ξ
only-∙ (zero x) (zero y) (zero z) sp rewrite ∙²-unique x ∙²-idʳ | ∙²-unique y ∙²-idʳ | ∙²-unique z ∙²-idʳ = ⊎-idˡ , sp
only-∙ (suc Γ≔) (suc Δ≔) (suc Ξ≔) sp = only-∙ Γ≔ Δ≔ Ξ≔ sp , ∙²-idˡ


diamond : {Γ Ξ Ψ : Ctx idxs}
        → i ≢ j
        → Γ ≔ x at j ⊠ Ξ
        → Γ ≔ y at i ⊠ Ψ
        → Σ[ Θ ∈ Ctx idxs ]
        ( Ξ ≔ y at i ⊠ Θ
        × Ψ ≔ x at j ⊠ Θ
        )
diamond i≢j (zero _) (zero _) = ⊥-elim (i≢j refl)
diamond i≢j (zero x) (suc ∋i) = _ , suc ∋i , zero x
diamond i≢j (suc ∋j) (zero x) = _ , zero x , suc ∋j
diamond i≢j (suc ∋j) (suc ∋i) with diamond (i≢j ∘ cong suc) ∋j ∋i
diamond i≢j (suc ∋j) (suc ∋i) | _ , ∋i' , ∋j' = _ , suc ∋i' , suc ∋j'

outer-diamond : {Γ Ξ Ψ Θ ΞΔ Δ ΨΔ : Ctx idxs}
              → i ≢ j
              → Γ ≔ x at i ⊠ Ξ
              → Γ ≔ y at j ⊠ Ψ
              → Ξ ≔ y at j ⊠ Θ
              → Ψ ≔ x at i ⊠ Θ
              → Ξ ≔ ΞΔ ⊎ Δ
              → Ψ ≔ ΨΔ ⊎ Δ
              → Σ[ ΘΔ ∈ Ctx idxs ] (Θ ≔ ΘΔ ⊎ Δ)
outer-diamond i≢j (zero _) (zero _) (zero _) (zero _) a b = ⊥-elim (i≢j refl)
outer-diamond i≢j (zero x₁) (suc ∋j) (suc ∈j) (zero x) (as , a) (bs , b) = _ , (bs , a)
outer-diamond i≢j (suc ∋i) (zero ∋j) (zero ∈j) (suc ∈i) (as , a) (bs , b) = _ , (as , b)
outer-diamond i≢j (suc ∋i) (suc ∋j) (suc ∈j) (suc ∈i) (as , a) (bs , b) with outer-diamond (i≢j ∘ cong suc) ∋i ∋j ∈j ∈i as bs
outer-diamond i≢j (suc ∋i) (suc ∋j) (suc ∈j) (suc ∈i) (as , a) (bs , b) | _ , s = _ , (s , a)


-- TODO: generalize to contexts
reverse : {Γ Ξ Ψ : Ctx idxs}
        → Γ ≔ x at i ⊠ Ξ
        → Ξ ≔ y at j ⊠ Ψ
        → Σ[ Θ ∈ Ctx idxs ]
        ( Γ ≔ y at j ⊠ Θ
        × Θ ≔ x at i ⊠ Ψ
        )
reverse (zero x) (zero y) =
  let _ , a , b = ∙²-assoc⁻¹ x (∙²-comm y) in
  _ , zero (∙²-comm a) , zero b
reverse (zero x) (suc ∋j) = _ , suc ∋j , zero x
reverse (suc ∋i) (zero x) = _ , zero x , suc ∋i
reverse (suc ∋i) (suc ∋j) with reverse ∋i ∋j
reverse (suc ∋i) (suc ∋j) | _ , ∋i' , ∋j' = _ , suc ∋i' , suc ∋j'

boil : {Γ Ξ Θ Ψ ΘΨ : Ctx idxs}
     → Γ ≔ x at i ⊠ Θ
     → Γ ≔ y at i ⊠ Ξ
     → Ξ ≔ z at i ⊠ Ψ
     → Θ ≔ ΘΨ ⊎ Ψ
     → All.lookup i ΘΨ ≡ ℓ∅
     → x ≔ y ∙² z
boil {i = zero} (zero a) (zero b) (zero c) (_ , d) refl rewrite ∙²-unique d ∙²-idˡ with ∙²-assoc⁻¹ b c
boil {i = zero} (zero a) (zero b) (zero c) (_ , d) refl | _ , e , f rewrite ∙²-uniqueˡ e a = f
boil {i = suc i} (suc a) (suc b) (suc c) (d , _) eq = boil a b c d eq

tail-ℓ∅ : {Γ ΓΨ Ψ ΓΘ Θ ΘΨ : Ctx idxs}
        → Γ ≔ ΓΨ ⊎ Ψ
        → Γ ≔ ΓΘ ⊎ Θ
        → Θ ≔ ΘΨ ⊎ Ψ
        → All.lookup i ΓΨ ≡ ℓ∅
        → All.lookup i ΘΨ ≡ ℓ∅
tail-ℓ∅ {i = zero} (a , x) (b , y) (c , z) refl rewrite ∙²-unique x ∙²-idˡ with ∙²-mut-cancel y z
tail-ℓ∅ {i = zero} (a , x) (b , y) (c , z) refl | refl = ∙²-uniqueˡ z ∙²-idˡ
tail-ℓ∅ {i = suc i} (a , _) (b , _) (c , _) eq = tail-ℓ∅ a b c eq


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

mult-insert : (i : Fin (suc n)) → (Carrier idx) ² → Ctx idxs → Ctx (Vec.insert idxs i idx)
mult-insert zero xs' Γ = Γ -, xs'
mult-insert (suc i) xs' (Γ -, xs) = mult-insert i xs' Γ -, xs

mult-remove : Ctx idxs → (i : Fin (suc n)) → Ctx (Vec.remove idxs i)
mult-remove (Γ -, _) zero = Γ
mult-remove (Γ -, ys -, xs) (suc i) = mult-remove (Γ -, ys) i -, xs

mult-update : (i : Fin n) → (Carrier (Vec.lookup idxs i)) ² → Ctx idxs → Ctx idxs
mult-update zero m' (ms -, m) = ms -, m'
mult-update (suc i) m' (ms -, m) = mult-update i m' ms -, m
