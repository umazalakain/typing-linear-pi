open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)

import Data.Nat.Base as ℕ
import Data.Unit.Base as Unit
import Data.Empty as Empty
import Data.Nat.Properties as ℕₚ
import Data.Vec.Base as Vec
import Data.Vec.Properties as Vecₚ
import Data.Vec.Relation.Unary.All as All
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
import Data.Product as Product

open Empty using (⊥)
open Unit using (⊤; tt)
open Product using (Σ; _×_; _,_; proj₁; proj₂)
open ℕ using (ℕ; zero; suc)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Pointwise using (Pointwise; []; _∷_)

open import PiCalculus.Function using (_⊗_; _&_)

module PiCalculus.LinearTypeSystem.OmegaNat where

data MType : Set where
  nonlin lin : MType

data ωℕ : MType → Set where
  n∙ : ℕ → ωℕ lin
  ω∙ : ωℕ nonlin

pattern 0∙ = n∙ 0
pattern 1∙ = n∙ 1

private
  variable
    n : ℕ
    M N : MType

_+_ : ωℕ M → ωℕ M → ωℕ M
n∙ x + n∙ y = n∙ (x ℕ.+ y)
ω∙ + ω∙ = ω∙

+-idˡ : ∀ x → 0∙ + x ≡ x
+-idˡ (n∙ _) = refl

+-idʳ : ∀ x → x + 0∙ ≡ x
+-idʳ (n∙ x) rewrite ℕₚ.+-identityʳ x = refl

+-ωʳ : ∀ x → x + ω∙ ≡ ω∙
+-ωʳ ω∙ = refl

+-comm : (x y : ωℕ M) → x + y ≡ y + x
+-comm (n∙ x) (n∙ y) rewrite ℕₚ.+-comm x y = refl
+-comm ω∙ ω∙ = refl

+-+-assoc : (x y z : ωℕ M) → (x + y) + z ≡ x + (y + z)
+-+-assoc (n∙ x) (n∙ y) (n∙ z) rewrite ℕₚ.+-assoc x y z = refl
+-+-assoc ω∙ ω∙ ω∙ = refl

ω0 : ωℕ M
ω0 {nonlin} = ω∙
ω0 {lin} = 0∙

ω1 : ωℕ M
ω1 {nonlin} = ω∙
ω1 {lin} = 1∙

ω0s : {Ms : Vec MType n} → All ωℕ Ms
ω0s {_} {[]} = []
ω0s {_} {_ ∷ _} = ω0 ∷ ω0s

_+ᵥ_ : {Ms : Vec MType n} → All ωℕ Ms → All ωℕ Ms → All ωℕ Ms
[] +ᵥ [] = []
(x ∷ xs) +ᵥ (y ∷ ys) = x + y ∷ xs +ᵥ ys
