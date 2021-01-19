{-# OPTIONS --safe #-} -- --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (fromWitness)

import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Unit as Unit
import Data.Nat as ℕ
import Data.Vec as Vec
import Data.Fin as Fin
import Data.Vec.Relation.Unary.All as All

open Unit using (⊤; tt)
open ℕ using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import PiCalculus.Syntax
open Scoped
open import PiCalculus.Semantics
open import PiCalculus.Semantics.Properties
open import PiCalculus.LinearTypeSystem.Algebras


module PiCalculus.LinearTypeSystem.SubjectCongruence (Ω : Algebras) where
open Algebras Ω
open import PiCalculus.LinearTypeSystem Ω
open import PiCalculus.LinearTypeSystem.ContextLemmas Ω
open import PiCalculus.LinearTypeSystem.Framing Ω
open import PiCalculus.LinearTypeSystem.Weakening Ω
open import PiCalculus.LinearTypeSystem.Strengthening Ω
open import PiCalculus.LinearTypeSystem.Exchange Ω

SubjectCongruence : Set
SubjectCongruence = {n : ℕ} {γ : PreCtx n} {idxs : Idxs n} {Γ Δ : Ctx idxs}
                  → {r : RecTree} {P Q : Scoped n}
                  → P ≅⟨ r ⟩ Q
                  → γ ； Γ ⊢ P ▹ Δ
                  → γ ； Γ ⊢ Q ▹ Δ

private
  variable
    n m : ℕ
    P Q : Scoped n

comp-comm : {γ : PreCtx n} {idxs : Idxs n} {Γ Ξ : Ctx idxs}
          → γ ； Γ ⊢ P ∥ Q ▹ Ξ
          → γ ； Γ ⊢ Q ∥ P ▹ Ξ
comp-comm (⊢P ∥ ⊢Q) with ⊢-⊗ ⊢P | ⊢-⊗ ⊢Q
comp-comm (⊢P ∥ ⊢Q) | _ , P≔ | _ , Q≔ =
  let _ , (Q'≔ , P'≔) = ⊗-assoc (⊗-comm P≔) Q≔ in
  ⊢-frame Q≔ Q'≔ ⊢Q ∥ ⊢-frame P≔ (⊗-comm P'≔) ⊢P

import Relation.Binary.HeterogeneousEquality as Heq

dropᵥ : ∀ {a} {A : Set a} (n : ℕ) (xs : Vec A (n ℕ.+ m)) → Vec A m
dropᵥ zero xs = xs
dropᵥ (suc n) (x ∷ xs) = dropᵥ n xs

drop : ∀ {a p} {A : Set a} {P : A → Set p}
     → (n : ℕ) {m : ℕ} {xs : Vec A (n ℕ.+ m)} (ps : All P xs)
     → All P (dropᵥ n xs)
drop zero ps = ps
drop (suc n) {xs = x ∷ xs}(p ∷ ps) = drop n ps

module _ {a p} {A : Set a} {P : A → Set p} where
  data PHEq : ∀ {m n} {xs : Vec A m} {ys : Vec A n} (pxs : All P xs) (pys : All P ys) → Set p where
    []  : PHEq [] []
    _∷_ : ∀ {m n x} {px py : P x} {xs : Vec A m} {ys : Vec A n} {pxs : All P xs} {pys : All P ys}
          (px∼py : px ≡ py) (pxs∼pys : PHEq pxs pys) →
          PHEq (px ∷ pxs) (py ∷ pys)

  PHEq-to-≡ : {xs : Vec A n} {pxs : All P xs} {pys : All P xs} → PHEq pxs pys → pxs ≡ pys
  PHEq-to-≡ [] = refl
  PHEq-to-≡ (px∼py ∷ pheq) = cong₂ _∷_ px∼py (PHEq-to-≡ pheq)

  PHEq-refl : {xs : Vec A n} {pxs : All P xs} → PHEq pxs pxs
  PHEq-refl {pxs = []} = []
  PHEq-refl {pxs = px ∷ pxs} = refl ∷ PHEq-refl

∋-unique : {γ ξ : PreCtx (n ℕ.+ m)} {is js : Idxs (n ℕ.+ m)} {Γ Δ : Ctx is} {Ξ Ω : Ctx js}
         → {i : Fin (n ℕ.+ m)} {t₁ t₂ : Type} {id jd : Idx} {u₁ : Usage id ²} {u₂ : Usage jd ²}
         → γ ； Γ ∋[ i ] t₁ ； u₁ ▹ Δ
         → ξ ； Ξ ∋[ i ] t₂ ； u₂ ▹ Ω
         → dropᵥ n γ ≡ dropᵥ n ξ
         → (id ≡ jd → u₁ Heq.≅ u₂)
         → PHEq (drop n Δ) (drop n Ω)
         → PHEq (drop n Γ) (drop n Ξ)
∋-unique {zero} {is = _} {.(_ -, _)} {i = .zero} (zero , zero x) (zero , zero x') refl ueq (refl ∷ eq) rewrite Heq.≅-to-≡ (ueq refl) = ∙²-unique x x' ∷ eq
∋-unique {zero} {is = is} {js} {i = .(suc _)} (suc fst , suc snd) (suc fst₁ , suc snd₁) refl ueq (px∼py ∷ eq) = px∼py ∷ (∋-unique (fst , snd) (fst₁ , snd₁) refl ueq eq)
∋-unique {suc n} {i = i} (zero , zero x) (zero , zero x') qe ueq eq = eq
∋-unique {suc n} {i = i} (suc tx , suc ux) (suc ty , suc uy) = ∋-unique (tx , ux) (ty , uy)

⊢-unique : {γ ξ : PreCtx (n ℕ.+ m)} {is js : Idxs (n ℕ.+ m)} {Γ Δ : Ctx is} {Ξ Ω : Ctx js}
         → γ ； Γ ⊢ P ▹ Δ
         → ξ ； Ξ ⊢ P ▹ Ω
         → dropᵥ n γ ≡ dropᵥ n ξ
         → PHEq (drop n Δ) (drop n Ω)
         → PHEq (drop n Γ) (drop n Ξ)
⊢-unique 𝟘 𝟘 qe eq = eq
⊢-unique (ν t m μ Γ⊢) (ν _ _ _ Ξ⊢) = ⊢-unique Γ⊢ Ξ⊢
⊢-unique (x ⦅⦆ Γ⊢) (x' ⦅⦆ Ξ⊢) qe eq = ∋-unique x x' qe (λ {refl → Heq.refl}) (⊢-unique Γ⊢ Ξ⊢ qe eq)
⊢-unique (Γx ⟨ Γy ⟩ Γ⊢) (Ξx ⟨ Ξy ⟩ Ξ⊢) qe eq = ∋-unique Γx Ξx qe (λ {refl → Heq.refl}) (∋-unique Γy Ξy qe (λ {refl → {!Heq.refl!}}) {!!})
⊢-unique (Γ⊢P ∥ Γ⊢Q) (Ξ⊢P ∥ Ξ⊢Q) qe eq = ⊢-unique Γ⊢P Ξ⊢P qe (⊢-unique Γ⊢Q Ξ⊢Q qe eq)
⊢-unique (! Γ⊢) (! Ξ⊢) = ⊢-unique Γ⊢ Ξ⊢

subject-cong : SubjectCongruence
subject-cong (stop comp-assoc) (⊢P ∥ (⊢Q ∥ ⊢R)) = (⊢P ∥ ⊢Q) ∥ ⊢R
subject-cong (stop comp-symm) (⊢P ∥ ⊢Q) = comp-comm (⊢P ∥ ⊢Q)
subject-cong (stop comp-end) (⊢P ∥ 𝟘) = ⊢P
subject-cong (stop replicate) (! ⊢P) = ⊢P ∥ (! ⊢P)
subject-cong (stop scope-end) (ν t c ._ 𝟘) = 𝟘
subject-cong (stop (scope-ext u)) (ν t c μ (_∥_ {Δ = _ -, _} ⊢P ⊢Q)) rewrite sym (⊢-unused _ u ⊢P) = ⊢-strengthen zero u ⊢P ∥ ν t c μ ⊢Q
subject-cong (stop scope-scope-comm) (ν t c μ (ν t₁ c₁ μ₁ ⊢P)) = ν t₁ c₁ μ₁ (ν t c μ (⊢-exchange zero ⊢P))
subject-cong (cong-symm (stop comp-assoc)) ((⊢P ∥ ⊢Q) ∥ ⊢R) = ⊢P ∥ (⊢Q ∥ ⊢R)
subject-cong (cong-symm (stop comp-symm)) (⊢P ∥ ⊢Q) = comp-comm (⊢P ∥ ⊢Q)
subject-cong (cong-symm (stop replicate)) (⊢P ∥ ! !⊢P) rewrite PHEq-to-≡ (⊢-unique {n = 0} ⊢P !⊢P refl PHEq-refl) = ! !⊢P
subject-cong (cong-symm (stop comp-end)) ⊢P = ⊢P ∥ 𝟘
subject-cong (cong-symm (stop scope-end)) 𝟘 = ν 𝟙 {∃Idx} (0∙ , 0∙) {∃Idx} 0∙ 𝟘
subject-cong (cong-symm (stop (scope-ext u))) (⊢P ∥ (ν t c μ ⊢Q)) = ν t c μ ((subst (λ ● → _ ； _ ⊢ ● ▹ _) (lift-lower zero _ u) (⊢-weaken zero ⊢P)) ∥ ⊢Q)
subject-cong (cong-symm (stop scope-scope-comm)) (ν t c μ (ν t₁ c₁ μ₁ ⊢P)) = ν _ _ _ (ν _ _ _ (subst (λ ● → _ ； _ ⊢ ● ▹ _) (exchange-exchange zero _) (⊢-exchange zero ⊢P)))

-- Equivalence and congruence
subject-cong cong-refl ⊢P = ⊢P
subject-cong (cong-trans P≅Q Q≅R) ⊢P = subject-cong Q≅R (subject-cong P≅Q ⊢P)
subject-cong (ν-cong P≅Q) (ν t m μ ⊢P) = ν t m μ (subject-cong P≅Q ⊢P)
subject-cong (comp-cong P≅Q) (⊢P ∥ ⊢R) = subject-cong P≅Q ⊢P ∥ ⊢R
subject-cong (input-cong P≅Q) (x ⦅⦆ ⊢P) = x ⦅⦆ subject-cong P≅Q ⊢P
subject-cong (output-cong P≅Q) (x ⟨ y ⟩ ⊢P) = x ⟨ y ⟩ subject-cong P≅Q ⊢P
subject-cong (cong-symm cong-refl) ⊢P = ⊢P
subject-cong (cong-symm (cong-symm P≅Q)) ⊢P = subject-cong P≅Q ⊢P
subject-cong (cong-symm cong-trans P≅Q P≅R) ⊢P = subject-cong (cong-symm P≅Q) (subject-cong (cong-symm P≅R) ⊢P)
subject-cong (cong-symm (ν-cong P≅Q)) (ν t m μ ⊢P) = ν t m μ (subject-cong (cong-symm P≅Q) ⊢P)
subject-cong (cong-symm (comp-cong P≅Q)) (⊢P ∥ ⊢R) = subject-cong (cong-symm P≅Q) ⊢P ∥ ⊢R
subject-cong (cong-symm (input-cong P≅Q)) (x ⦅⦆ ⊢P) = x ⦅⦆ subject-cong (cong-symm P≅Q) ⊢P
subject-cong (cong-symm (output-cong P≅Q)) (x ⟨ y ⟩ ⊢P) = x ⟨ y ⟩ subject-cong (cong-symm P≅Q) ⊢P
