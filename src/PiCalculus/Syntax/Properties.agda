{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)

import Data.List.Base as List
import Data.List.Properties as Listₚ
import Data.List.Membership.Propositional as ∈ₗ
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕₚ
import Data.String.Base as String
import Data.Product.Properties as Productₚ
import Data.Vec.Base as Vec
import Data.Vec.Relation.Unary.Any as Any
import Data.Vec.Membership.Propositional as ∈ᵥ
import Data.Vec.Membership.Propositional.Properties as ∈ᵥₚ
import Data.String.Properties as Stringₚ

open Vec using ([]; _∷_; Vec)
open String using (String)
open ℕ using (ℕ; zero; suc)
open Any using (here; there)
open List using (List; []; _∷_; [_])

open import PiCalculus.Syntax
open Raw
open Scoped
open Conversion

open import PiCalculus.Utils
open AllAcc using ([]; _∷_)

module PiCalculus.Syntax.Properties where

module _ where
  private
    variable
      n : ℕ
      P Q R S : Scoped n
      namex namey : Name

  fromName∘toName : (i : Fin n) (ctx : Ctx n) → ∈toFin (∈ᵥₚ.∈-lookup i ctx) ≡ i
  fromName∘toName zero (x ∷ ctx) = refl
  fromName∘toName (suc i) (x ∷ ctx) rewrite fromName∘toName i ctx = refl

  toName∘fromName : ∀ {x} {ctx : Ctx n} (x∈ctx : x ∈ᵥ.∈ ctx) → Vec.lookup ctx (∈toFin x∈ctx) ≡ x
  toName∘fromName (here px) = sym px
  toName∘fromName (there x∈ctx) = toName∘fromName x∈ctx

  postulate
    -- PR agda accepted, landing in 2.6.2 https://github.com/agda/agda/pull/4790
    fromList-injective : ∀ a b → String.fromList a ≡ String.fromList b → a ≡ b

  -- The circum (^) is not a decimal character
  ^∉DECIMALS : '^' ∈ᵥ.∉ ℕₛ.DECIMALS
  ^∉DECIMALS (there (there (there (there (there (there (there (there (there (there ()))))))))))

  -- In <name>^<natural> the <natural> does not contain ^, therefore toString is injective
  toString-injective : (x y : Name × ℕ) → toString x ≡ toString y → x ≡ y
  toString-injective (nx , cx) (ny , cy) eq = cong₂ _,_ strip-toList strip-toDecimalChars
    where
      strip-fromList = fromList-injective (toCharList (nx , cx)) (toCharList (ny , cy)) eq
      count-repr = ListInv.inv-++ʳ (String.toList nx) (String.toList ny) '^'
                                  (^∉DECIMALS ∘ (ℕₛ.∈toDigitChars⇒∈digitChars cx '^'))
                                  (^∉DECIMALS ∘ (ℕₛ.∈toDigitChars⇒∈digitChars cy '^'))
                                  strip-fromList
      strip-toDecimalChars = ℕₛ.toDigitChars-injective cx cy count-repr
      cancel-names = Listₚ.++-cancelʳ (String.toList nx) (String.toList ny)
                                      (subst (λ ● → String.toList nx List.++ ('^' ∷ ●) ≡ _)
                                            count-repr strip-fromList)
      strip-toList = Stringₚ.toList-injective nx ny cancel-names


  -- A fresh variable name created from inspecting a context cannot be in that context
  fresh-∉' : ∀ m name (xs : Ctx n) (isf : Fresh xs) → toString (name , m ℕ.+ (count name xs)) ∈ᵥ.∉ apply isf
  fresh-∉' m name (x ∷ xs) ((._ , refl) ∷ ps) (here seq) with x Stringₚ.≟ name
  ... | yes refl = ℕₚ.m≢1+n+m _ (begin
    count name xs
      ≡˘⟨ Productₚ.,-injectiveʳ (toString-injective (name , m ℕ.+ suc (count name xs)) (name , count name xs) seq) ⟩
    m ℕ.+ suc (count name xs)
      ≡⟨ ℕₚ.+-suc m _ ⟩
    suc m ℕ.+ count name xs
      ∎)
  ... | no ¬q = ¬q (Productₚ.,-injectiveˡ (sym (toString-injective (name , m ℕ.+ count name xs) (x , count x xs) seq)))
  fresh-∉' m name (x ∷ xs) (_ ∷ _) (there ∈ps) with x Stringₚ.≟ name
  fresh-∉' m name (x ∷ xs) (_ ∷ _) (there ∈ps) | yes refl rewrite ℕₚ.+-suc m (count name xs) = fresh-∉' (suc m) name _ _ ∈ps
  fresh-∉' m name (x ∷ xs) (_ ∷ _) (there ∈ps) | no ¬q = fresh-∉' m name _ _ ∈ps

  fresh-∉ : ∀ name {xs : Ctx n} (isf : Fresh xs) → toString (name , count name xs) ∈ᵥ.∉ apply isf
  fresh-∉ name {xs} isf = fresh-∉' zero name xs isf

  -- Translating from de Bruijn to names results in a well-scoped process

  toRaw-WellScoped : {ctx : Ctx n} (fP : Fresh ctx) (P : Scoped n) → WellScoped (apply fP) (toRaw fP P)
  toRaw-WellScoped {ctx = ctx} fP 𝟘 = tt
  toRaw-WellScoped {ctx = ctx} fP (υ P ⦃ name ⦄) = toRaw-WellScoped (fresh name ctx ∷ fP) P
  toRaw-WellScoped {ctx = ctx} fP (P ∥ Q) = toRaw-WellScoped fP P , toRaw-WellScoped fP Q
  toRaw-WellScoped {ctx = ctx} fP ((x ⦅⦆ P) ⦃ name ⦄) = ∈ᵥₚ.∈-lookup _ _ , toRaw-WellScoped (fresh name ctx ∷ fP) P
  toRaw-WellScoped {ctx = ctx} fP (x ⟨ y ⟩ P) = ∈ᵥₚ.∈-lookup _ _ , ∈ᵥₚ.∈-lookup _ _ , toRaw-WellScoped fP P

  -- Translating from de Bruijn to names results in no shadowed variables

  toRaw-NotShadowed : {ctx : Ctx n} (fP : Fresh ctx) (P : Scoped n) → NotShadowed (apply fP) (toRaw fP P)
  toRaw-NotShadowed {ctx = ctx} fP 𝟘 = tt
  toRaw-NotShadowed {ctx = ctx} fP (υ P ⦃ name ⦄) = fresh-∉ name fP , (toRaw-NotShadowed (_ ∷ fP) P)
  toRaw-NotShadowed {ctx = ctx} fP (P ∥ Q) = toRaw-NotShadowed fP P , toRaw-NotShadowed fP Q
  toRaw-NotShadowed {ctx = ctx} fP ((x ⦅⦆ P) ⦃ name ⦄) = fresh-∉ name fP , toRaw-NotShadowed (fresh name ctx ∷ fP) P
  toRaw-NotShadowed {ctx = ctx} fP (x ⟨ y ⟩ P) = toRaw-NotShadowed fP P

  -- Translating from de Bruijn to names and back results in the same process modulo name hints

  data _Nameless≡_ {n} : Scoped n → Scoped n → Set where
    inaction : 𝟘 Nameless≡ 𝟘
    scope : P Nameless≡ Q → υ P ⦃ namex ⦄ Nameless≡ υ Q ⦃ namey ⦄
    comp : P Nameless≡ Q → R Nameless≡ S → (P ∥ R) Nameless≡ (Q ∥ S)
    input : ∀ {x} → P Nameless≡ Q → (x ⦅⦆ P) ⦃ namex ⦄ Nameless≡ (x ⦅⦆ Q) ⦃ namey ⦄
    output : ∀ {x y} → P Nameless≡ Q → (x ⟨ y ⟩ P) Nameless≡ (x ⟨ y ⟩ Q)

  fromRaw∘toRaw : {ctx : Ctx n} (isf : Fresh ctx) (P : Scoped n)
                → fromRaw' (apply isf) (toRaw isf P) (toRaw-WellScoped isf P) Nameless≡ P
  fromRaw∘toRaw isf 𝟘 = inaction
  fromRaw∘toRaw {ctx = ctx} isf (υ P ⦃ name ⦄) =
    scope (fromRaw∘toRaw (fresh name ctx ∷ isf) P)
  fromRaw∘toRaw isf (P ∥ Q) =
    comp (fromRaw∘toRaw isf P) (fromRaw∘toRaw isf Q)
  fromRaw∘toRaw {ctx = ctx} isf ((x ⦅⦆ P) ⦃ name ⦄)
    rewrite fromName∘toName x (apply isf) =
    input (fromRaw∘toRaw (fresh name ctx ∷ isf) P)
  fromRaw∘toRaw {ctx = ctx} isf (x ⟨ y ⟩ P)
    rewrite fromName∘toName x (apply isf) | fromName∘toName y (apply isf) =
    output (fromRaw∘toRaw isf P)


module _ where
  private
    variable
      n : ℕ
      P Q R S : Raw
      x y w z : Name
      ks vs : Ctx n

  _∈²_ : ∀ {n} → (Name × Name) → (Ctx n × Ctx n) → Set
  (x , y ) ∈² (xs , ys) = Σ[ i ∈ Fin _ ] (Vec.lookup xs i ≡ x × Vec.lookup ys i ≡ y)

  infix 5 _α[_↦_]≡_
  data _α[_↦_]≡_ : Raw → ∀ {n} → Ctx n → Ctx n → Raw → Set where
    inaction : 𝟘 α[ ks ↦ vs ]≡ 𝟘
    scope    : P α[ x ∷ ks ↦ y ∷ vs ]≡ Q
             → ⦅υ x ⦆ P α[ ks ↦ vs ]≡ ⦅υ y ⦆ Q
    comp     : P α[ ks ↦ vs ]≡ Q
             → R α[ ks ↦ vs ]≡ S
             → P ∥ R α[ ks ↦ vs ]≡ Q ∥ S
    input    : (x , y) ∈² (ks , vs)
             → P α[ w ∷ ks ↦ z ∷ vs ]≡ Q
             → x ⦅ w ⦆ P α[ ks ↦ vs ]≡ y ⦅ z ⦆ Q
    output   : (x , y) ∈² (ks , vs)
             → (w , z) ∈² (ks , vs)
             → P α[ ks ↦ vs ]≡ Q
             → x ⟨ w ⟩ P α[ ks ↦ vs ]≡ (y ⟨ z ⟩ Q)

  -- Translating a well-scoped process to de Bruijn and back results in the same process
  -- modulo alpha renaming, where the new names in `apply isf` map to the old in `ctx`

  toRaw∘fromRaw : {ctx : Ctx n} (isf : Fresh ctx) (P : Raw) (wsP : WellScoped ctx P)
                → toRaw isf (fromRaw' ctx P wsP) α[ apply isf ↦ ctx ]≡ P
  toRaw∘fromRaw isf 𝟘 wsP = inaction
  toRaw∘fromRaw {ctx = ctx} isf (⦅υ x ⦆ P) wsP
    = scope (toRaw∘fromRaw (fresh x ctx ∷ isf) P wsP)
  toRaw∘fromRaw isf (P ∥ Q) (wsP , wsQ)
    = comp (toRaw∘fromRaw isf P wsP)
           (toRaw∘fromRaw isf Q wsQ)
  toRaw∘fromRaw {ctx = ctx} isf (x ⦅ y ⦆ P) (x∈ctx , wsP)
    = input (_ , refl , toName∘fromName x∈ctx)
            (toRaw∘fromRaw (fresh y ctx ∷ isf) P wsP)
  toRaw∘fromRaw isf (x ⟨ y ⟩ P) (x∈ctx , y∈ctx , wsP)
    = output (_ , refl , toName∘fromName x∈ctx)
             (_ , refl , toName∘fromName y∈ctx)
             (toRaw∘fromRaw isf P wsP)
