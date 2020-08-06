{-# OPTIONS --safe #-} -- --without-K #-}

open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; inspect; [_])
open import Relation.Nullary.Negation using (contradiction)

open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
import Data.Sum.Properties as Sumₚ
import Data.Vec.Properties as Vecₚ
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Vec.Relation.Unary.All.Properties as Allₚ
import Data.Vec.Relation.Binary.Equality.Propositional as ≋
import Data.Vec.Functional.Relation.Binary.Pointwise


open import PiCalculus.Syntax
open Scoped
open import PiCalculus.Semantics
import PiCalculus.Utils
open PiCalculus.Utils.Sum
open PiCalculus.Utils.All2Vec

module PiCalculus.Semantics.Properties where
private
  variable
    n m l : ℕ
    i j : Fin n
    P : Scoped n

punchInFin∘invert : ∀ x {y} (ρ : n + m ≔ l) → invert ρ x ≡ inj₁ y → punchInFin ρ y ≡ x
punchInFin∘invert zero (left ρ) refl = refl
punchInFin∘invert (suc x) (left ρ) eq with invert ρ x | inspect (invert ρ) x
punchInFin∘invert (suc x) (left ρ) refl | inj₁ _ | [ eq ] = cong suc (punchInFin∘invert x ρ eq)
punchInFin∘invert (suc x) (right ρ) eq with invert ρ x | inspect (invert ρ) x
punchInFin∘invert (suc x) (right ρ) refl | inj₁ _ | [ qe ] = cong suc (punchInFin∘invert x ρ qe)

invert∘punchInFin : ∀ (ρ : n + m ≔ l) i → invert ρ (punchInFin (+-comm ρ) i) ≡ inj₂ i
invert∘punchInFin (left ρ) i rewrite invert∘punchInFin ρ i = refl
invert∘punchInFin (right ρ) zero = refl
invert∘punchInFin (right ρ) (suc i) rewrite invert∘punchInFin ρ i = refl

------------------------------------------------------------
-- punchIn and punchOut are inverses

punchInFin∘punchOutFin : (ρ : n + m ≔ l) (x : Fin l) (ilx : IsLeftFin ρ x)
                       → punchInFin ρ (punchOutFin ρ x ilx) ≡ x
punchInFin∘punchOutFin (left ρ) zero (.zero , refl) = refl
punchInFin∘punchOutFin (left ρ) (suc x) ilx with invert ρ x | inspect (invert ρ) x
punchInFin∘punchOutFin (left ρ) (suc x) (_ , refl) | inj₁ _ | [ eq ] = cong suc (punchInFin∘invert _ ρ eq)
punchInFin∘punchOutFin (right ρ) (suc x) ilx with invert ρ x | inspect (invert ρ) x
punchInFin∘punchOutFin (right ρ) (suc x) (_ , refl) | inj₁ _ | [ eq ] = cong suc (punchInFin∘invert _ ρ eq)


punchIn∘punchOut : (ρ : n + m ≔ l) (P : Scoped l) (ilP : IsLeft ρ P)
                 → punchIn ρ (punchOut ρ P ilP) ≡ P
punchIn∘punchOut ρ 𝟘 ilP = refl
punchIn∘punchOut ρ (ν P) ilP =
  cong (λ ● → ν ●) (punchIn∘punchOut (left ρ) P ilP)
punchIn∘punchOut ρ (P ∥ Q) (ilP , ilQ) =
  cong₂ _∥_ (punchIn∘punchOut ρ P ilP) (punchIn∘punchOut ρ Q ilQ)
punchIn∘punchOut ρ (x ⦅ m ⦆ P) (ilx , ilP) =
  cong₂ _⦅ m ⦆_ (punchInFin∘punchOutFin ρ x ilx) (punchIn∘punchOut (extend m ρ) P ilP)
punchIn∘punchOut ρ (x ⟨ ys ⟩ P) (ilx , ilys , ilP)
  rewrite punchIn∘punchOut ρ P ilP
  = cong₂ (_⟨_⟩ _) (punchInFin∘punchOutFin ρ x ilx) (helper ρ ilys)
  where
  helper : ∀ {k} (ρ : n + m ≔ l) {ys : Vec (Fin l) k} (ilys : All (IsInj₁ ∘ invert ρ) ys)
      → Vec.map (punchInFin ρ) (all2vec (λ {●} → punchOutFin ρ ●) ilys) ≡ ys
  helper ρ [] = refl
  helper ρ (px ∷ pxs) = cong₂ _∷_ (punchInFin∘punchOutFin ρ _ px) (helper ρ pxs)

------------------------------------------------------------
-- Substituting by an empty set of variables

substFin-id : (ρ : n + zero ≔ l) (x : Fin l) → x [ ρ ↦ [] ]-Fin ≡ x
substFin-id ρ x with invert ρ x
substFin-id ρ x | inj₁ _ = refl

subst-id : (ρ : n + zero ≔ l) (P : Scoped l) → P [ ρ ↦ [] ] ≡ P
subst-id ρ 𝟘 = refl
subst-id ρ (ν P) = cong (λ ● → ν ●) (subst-id (left ρ) P)
subst-id ρ (P ∥ Q) = cong₂ _∥_ (subst-id ρ P) (subst-id ρ Q)
subst-id ρ (x ⦅ m ⦆ P) = cong₂ _⦅ m ⦆_ (substFin-id ρ x) (subst-id (extend m ρ) P)
subst-id ρ (x ⟨ ys ⟩ P) rewrite subst-id ρ P = cong₂ (_⟨_⟩ _) (substFin-id ρ x) (helper ρ ys)
  where
  helper : ∀ {k} (ρ : n + zero ≔ l) (ys : Vec (Fin l) k) → Vec.map (_[ ρ ↦ [] ]-Fin) ys ≡ ys
  helper ρ [] = refl
  helper ρ (y ∷ ys) = cong₂ _∷_ (substFin-id ρ y) (helper ρ ys)

invert-comm : (ρ : n + m ≔ l) (x : Fin l) → invert (+-comm ρ) x ≡ Sum.swap (invert ρ x)
invert-comm (left ρ) zero = refl
invert-comm (left ρ) (suc x) with invert ρ x | inspect (invert ρ) x | invert (+-comm ρ) x | inspect (invert (+-comm ρ)) x
invert-comm (left ρ) (suc x) | inj₁ x₁ | [ eq ] | inj₁ x₂ | [ qe ] with invert-comm ρ x
invert-comm (left ρ) (suc x) | inj₁ x₁ | [ eq ] | inj₁ x₂ | [ qe ] | qee rewrite qe | eq = contradiction qee λ ()
invert-comm (left ρ) (suc x) | inj₁ x₁ | [ eq ] | inj₂ y | [ qe ] with invert-comm ρ x
invert-comm (left ρ) (suc x) | inj₁ x₁ | [ eq ] | inj₂ y | [ qe ] | qee rewrite qe | eq = cong (Sum.map id suc) qee
invert-comm (left ρ) (suc x) | inj₂ y | [ eq ] | inj₁ x₁ | [ qe ] with invert-comm ρ x
invert-comm (left ρ) (suc x) | inj₂ y | [ eq ] | inj₁ x₁ | [ qe ] | qee rewrite qe | eq = cong (Sum.map id suc) qee
invert-comm (left ρ) (suc x) | inj₂ y | [ eq ] | inj₂ y₁ | [ qe ] with invert-comm ρ x
invert-comm (left ρ) (suc x) | inj₂ y | [ eq ] | inj₂ y₁ | [ qe ] | qee rewrite qe | eq = contradiction qee λ ()
invert-comm (right ρ) zero = refl
invert-comm (right ρ) (suc x) with invert ρ x | inspect (invert ρ) x | invert (+-comm ρ) x | inspect (invert (+-comm ρ)) x
invert-comm (right ρ) (suc x) | inj₁ x₁ | [ eq ] | inj₁ x₂ | [ qe ] with invert-comm ρ x
invert-comm (right ρ) (suc x) | inj₁ x₁ | [ eq ] | inj₁ x₂ | [ qe ] | qee rewrite qe | eq = contradiction qee λ ()
invert-comm (right ρ) (suc x) | inj₁ x₁ | [ eq ] | inj₂ y | [ qe ] with invert-comm ρ x
invert-comm (right ρ) (suc x) | inj₁ x₁ | [ eq ] | inj₂ y | [ qe ] | qee rewrite qe | eq = cong (Sum.map suc id) qee
invert-comm (right ρ) (suc x) | inj₂ y | [ eq ] | inj₁ x₁ | [ qe ] with invert-comm ρ x
invert-comm (right ρ) (suc x) | inj₂ y | [ eq ] | inj₁ x₁ | [ qe ] | qee rewrite qe | eq = cong (Sum.map suc id) qee
invert-comm (right ρ) (suc x) | inj₂ y | [ eq ] | inj₂ y₁ | [ qe ] with invert-comm ρ x
invert-comm (right ρ) (suc x) | inj₂ y | [ eq ] | inj₂ y₁ | [ qe ] | qee rewrite qe | eq = contradiction qee λ ()

------------------------------------------------------------
-- exchange is involutive

neg-involutive : ∀ i → neg (neg i) ≡ i
neg-involutive zero = refl
neg-involutive (suc zero) = refl

exchangeFin-involutive : (ρ : n + 2 ≔ l) (x : Fin l) → exchangeFin ρ (exchangeFin ρ x) ≡ x
exchangeFin-involutive ρ x with invert ρ x | inspect (invert ρ) x
exchangeFin-involutive ρ x | inj₁ x₁ | [ eq ] rewrite eq = refl
exchangeFin-involutive ρ x | inj₂ y | [ eq ] with invert ρ (punchInFin (+-comm ρ) (neg y)) | inspect (invert ρ) (punchInFin (+-comm ρ) (neg y))
exchangeFin-involutive ρ x | inj₂ y | [ eq ] | inj₁ x₁ | [ qe ] rewrite invert∘punchInFin ρ (neg y) = contradiction qe λ ()
exchangeFin-involutive ρ x | inj₂ y | [ eq ] | inj₂ y₁ | [ qe ]
  -- invert ρ -> neg -> punchIn (+-comm ρ) -> invert ρ -> neg -> punchIn (+-comm ρ)
  --   invert ρ (punchIn (+-comm ρ) i) ≡ inj₂ i
  -- invert ρ -> neg -> neg -> punchIn (+-comm ρ)
  --   neg neg
  -- invert ρ -> punchIn (+-comm ρ)
  --   invert ρ x ≡ inj₂ i → punchIn (+-comm ρ) i ≡ x
  -- id
  rewrite
    Sumₚ.inj₂-injective (trans (sym qe) (invert∘punchInFin ρ (neg y))) |
    neg-involutive y |
    punchInFin∘invert _ (+-comm ρ) (trans (invert-comm ρ x) (cong Sum.swap eq))
    = refl

exchange-involutive : (ρ : n + 2 ≔ l) (P : Scoped l) → exchange ρ (exchange ρ P) ≡ P
exchange-involutive ρ 𝟘 = refl
exchange-involutive ρ (ν P) =
  cong (λ ● → ν ●) (exchange-involutive (left ρ) P)
exchange-involutive ρ (P ∥ Q) =
  cong₂ _∥_ (exchange-involutive ρ P) (exchange-involutive ρ Q)
exchange-involutive ρ (x ⦅ m ⦆ P) =
  cong₂ _⦅ m ⦆_ (exchangeFin-involutive ρ x) (exchange-involutive (extend m ρ) P)
exchange-involutive ρ (x ⟨ ys ⟩ P) rewrite exchange-involutive ρ P =
  cong₂ (_⟨_⟩ _) (exchangeFin-involutive ρ x) (helper ρ ys)
  where
  helper : ∀ {k} (ρ : n + 2 ≔ l) (ys : Vec (Fin l) k) → Vec.map (exchangeFin ρ) (Vec.map (exchangeFin ρ) ys) ≡ ys
  helper ρ [] = refl
  helper ρ (y ∷ ys) = cong₂ _∷_ (exchangeFin-involutive ρ y) (helper ρ ys)
