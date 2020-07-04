{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_; _|>_)

import Data.Nat as ℕ

open import Level using (_⊔_)
open import Data.Empty using (⊥-elim)
open ℕ using (ℕ; zero; suc)

module PiCalculus.Utils where
  private
    variable
      n : ℕ

  module AllAcc {a b} {A : Set a} where
    import Data.Vec as Vec
    open Vec using (Vec; []; _∷_)

    -- Like Data.Vec.Relation.Unary.All, but we also depend on the list constructed so far
    data All (P : ∀ {n} → A → Vec A n → Set b) : ∀ {n} → Vec A n → Set (a ⊔ b) where
      [] : All P []
      _∷_ : ∀ {n x} {xs : Vec A n} → P x xs → All P xs → All P (x ∷ xs)

    open All public

    map : ∀ {c} {C : Set c} {P : ∀ {n} → A → Vec A n → Set b} {xs : Vec A n}
        → (∀ {n x} {xs : Vec A n} → P x xs → C) → All P xs → Vec C n
    map f [] = []
    map f (x ∷ ps) = (f x) ∷ map f ps


  module ListInv {a} {A : Set a} where
    import Data.List as List
    import Data.List.Properties as Listₚ
    import Data.List.Membership.Propositional.Properties as ∈ₚ
    import Data.List.Relation.Unary.Any.Properties as Anyₚ
    open import Data.List.Relation.Unary.Any using (Any; here; there)
    open import Data.List.Membership.Propositional using (_∈_; _∉_)
    open import Data.List.Relation.Binary.Equality.Propositional {A = A} using (_≋_; []; _∷_; ≋⇒≡; ≡⇒≋; ≋-refl)
    open List using (List; []; _∷_; [_]; _++_; _∷ʳ_)

    module _ {b} {P : A → Set b} where
      open import Data.Sum using (_⊎_; inj₁; inj₂)

      ∷ʳ→ : ∀ {x xs} → (P x ⊎ Any P xs) → Any P (xs ∷ʳ x)
      ∷ʳ→ (inj₁ x) = Anyₚ.++⁺ʳ _ (here x)
      ∷ʳ→ (inj₂ y) = Anyₚ.++⁺ˡ y

      Any-reverse : {xs : List A} → Any P xs → Any P (List.reverse xs)
      Any-reverse {xs = x ∷ xs} (here p) rewrite Listₚ.unfold-reverse x xs = ∷ʳ→ (inj₁ p)
      Any-reverse {xs = x ∷ xs} (there ps) rewrite Listₚ.unfold-reverse x xs = ∷ʳ→ (inj₂ (Any-reverse ps))

      reverse-Any : {xs : List A} → Any P (List.reverse xs) → Any P xs
      reverse-Any = subst (Any P) (Listₚ.reverse-involutive _) ∘ Any-reverse

    inv-++ˡ' : ∀ lx ly {rx ry} s → s ∉ lx → s ∉ ly → lx ++ [ s ] ++ rx ≋ ly ++ [ s ] ++ ry → lx ≋ ly
    inv-++ˡ' [] [] s ∉lx ∉ly eq = []
    inv-++ˡ' [] (x ∷ ly) .x ∉lx ∉ly (refl ∷ eq) = ⊥-elim (∉ly (here refl))
    inv-++ˡ' (x ∷ lx) [] .x ∉lx ∉ly (refl ∷ eq) = ⊥-elim (∉lx (here refl))
    inv-++ˡ' (x ∷ lx) (.x ∷ ly) s ∉lx ∉ly (refl ∷ eq)
      rewrite ≋⇒≡ (inv-++ˡ' lx ly s (∉lx ∘ there) (∉ly ∘ there) eq) = ≋-refl

    inv-++ˡ : ∀ lx ly {rx ry} s → s ∉ lx → s ∉ ly → lx ++ [ s ] ++ rx ≡ ly ++ [ s ] ++ ry → lx ≡ ly
    inv-++ˡ lx ly s ∉lx ∉ly = ≋⇒≡ ∘ inv-++ˡ' lx ly s ∉lx ∉ly ∘ ≡⇒≋

    reverse⁻ : ∀ {xs ys : List A} → List.reverse xs ≡ List.reverse ys → xs ≡ ys
    reverse⁻ = subst (_≡ _) (Listₚ.reverse-involutive _)
             ∘ subst (_ ≡_) (Listₚ.reverse-involutive _)
             ∘ cong List.reverse

    inv-++ʳ : ∀ lx ly {rx ry} s → s ∉ rx → s ∉ ry → lx ++ [ s ] ++ rx ≡ ly ++ [ s ] ++ ry → rx ≡ ry
    inv-++ʳ lx ly {rx} {ry} s ∉rx ∉ry
      = reverse⁻
      ∘ inv-++ˡ (List.reverse rx) (List.reverse ry) s (∉rx ∘ reverse-Any) (∉ry ∘ reverse-Any)
      ∘ subst (_ ≡_) (do-reverse ly _)
      ∘ subst (_≡ _) (do-reverse lx _)
      ∘ cong List.reverse

      where do-reverse : ∀ (lx rx : List A) {s}
                       → List.reverse (lx ++ [ s ] ++ rx) ≡ List.reverse rx ++ [ s ] ++ List.reverse lx
            do-reverse lx rx {s} = trans (Listₚ.reverse-++-commute lx _)
                                         (trans (cong (_++ List.reverse lx) (Listₚ.unfold-reverse s rx))
                                                (Listₚ.++-assoc (List.reverse rx) _ _))

