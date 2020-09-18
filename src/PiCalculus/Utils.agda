{-# OPTIONS --safe --without-K #-}

open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst₂)
open import Function using (_∘_)
open import Relation.Nullary.Negation using (contradiction)

module PiCalculus.Utils where

module ListInv {a} {A : Set a} where
  open import Data.List as List using (List; []; _∷_; [_]; _++_)
  import Data.List.Properties as Listₚ
  import Data.List.Membership.Propositional.Properties as ∈ₚ
  import Data.List.Relation.Unary.Any.Properties as Anyₚ
  open import Data.List.Relation.Unary.Any using (Any; here; there)
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Relation.Binary.Equality.Propositional {A = A} using (_≋_; []; _∷_; ≋⇒≡; ≡⇒≋; ≋-refl)

  inv-++ˡ' : ∀ lx ly {rx ry} s → s ∉ lx → s ∉ ly → lx ++ [ s ] ++ rx ≋ ly ++ [ s ] ++ ry → lx ≋ ly
  inv-++ˡ' [] [] s ∉lx ∉ly eq = []
  inv-++ˡ' [] (x ∷ ly) .x ∉lx ∉ly (refl ∷ eq) = contradiction (here refl) ∉ly
  inv-++ˡ' (x ∷ lx) [] .x ∉lx ∉ly (refl ∷ eq) = contradiction (here refl) ∉lx
  inv-++ˡ' (x ∷ lx) (.x ∷ ly) s ∉lx ∉ly (refl ∷ eq)
    rewrite ≋⇒≡ (inv-++ˡ' lx ly s (∉lx ∘ there) (∉ly ∘ there) eq) = ≋-refl

  inv-++ˡ : ∀ lx ly {rx ry} s → s ∉ lx → s ∉ ly → lx ++ [ s ] ++ rx ≡ ly ++ [ s ] ++ ry → lx ≡ ly
  inv-++ˡ lx ly s ∉lx ∉ly = ≋⇒≡ ∘ inv-++ˡ' lx ly s ∉lx ∉ly ∘ ≡⇒≋

  inv-++ʳ : ∀ lx ly {rx ry} s → s ∉ rx → s ∉ ry → lx ++ [ s ] ++ rx ≡ ly ++ [ s ] ++ ry → rx ≡ ry
  inv-++ʳ lx ly {rx} {ry} s ∉rx ∉ry
    = Listₚ.reverse-injective
    ∘ inv-++ˡ (List.reverse rx) (List.reverse ry) s (∉rx ∘ Anyₚ.reverse⁻) (∉ry ∘ Anyₚ.reverse⁻)
    ∘ subst₂ _≡_ (do-reverse lx _) (do-reverse ly _)
    ∘ cong List.reverse

    where do-reverse : ∀ (lx rx : List A) {s}
                     → List.reverse (lx ++ [ s ] ++ rx) ≡ List.reverse rx ++ [ s ] ++ List.reverse lx
          do-reverse lx rx {s} = trans (Listₚ.reverse-++-commute lx _)
                                       (trans (cong (_++ List.reverse lx) (Listₚ.unfold-reverse s rx))
                                              (Listₚ.++-assoc (List.reverse rx) _ _))
