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
      x y : Fin n
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
  fresh-∉' : ∀ m name (xs : Ctx n) → toString (name , m ℕ.+ (count name xs)) ∈ᵥ.∉ apply xs
  fresh-∉' m name (x ∷ xs) (here seq) with x Stringₚ.≟ name
  ... | yes refl = ℕₚ.m≢1+n+m _ (begin
    count name xs
      ≡˘⟨ Productₚ.,-injectiveʳ (toString-injective (name , m ℕ.+ suc (count name xs)) (name , count name xs) seq) ⟩
    m ℕ.+ suc (count name xs)
      ≡⟨ ℕₚ.+-suc m _ ⟩
    suc m ℕ.+ count name xs
      ∎)
  ... | no ¬q = ¬q (Productₚ.,-injectiveˡ (sym (toString-injective (name , m ℕ.+ count name xs) (x , count x xs) seq)))
  fresh-∉' m name (x ∷ xs) (there ∈ps) with x Stringₚ.≟ name
  fresh-∉' m name (x ∷ xs) (there ∈ps) | yes refl rewrite ℕₚ.+-suc m (count name xs) = fresh-∉' (suc m) name _ ∈ps
  fresh-∉' m name (x ∷ xs) (there ∈ps) | no ¬q = fresh-∉' m name _ ∈ps

  fresh-∉ : ∀ name (xs : Ctx n) → toString (name , count name xs) ∈ᵥ.∉ apply xs
  fresh-∉ name xs = fresh-∉' zero name xs

  -- Translating from de Bruijn to names results in a well-scoped process

  toRaw-WellScoped : (ctx : Ctx n) (P : Scoped n) → WellScoped (apply ctx) (toRaw ctx P)
  toRaw-WellScoped ctx 𝟘 = tt
  toRaw-WellScoped ctx (ν P ⦃ name ⦄) = toRaw-WellScoped (name ∷ ctx) P
  toRaw-WellScoped ctx (P ∥ Q) = toRaw-WellScoped ctx P , toRaw-WellScoped ctx Q
  toRaw-WellScoped ctx ((x ⦅⦆ P) ⦃ name ⦄) = ∈ᵥₚ.∈-lookup _ _ , toRaw-WellScoped (name ∷ ctx) P
  toRaw-WellScoped ctx (x ⟨ y ⟩ P) = ∈ᵥₚ.∈-lookup _ _ , ∈ᵥₚ.∈-lookup _ _ , toRaw-WellScoped ctx P

  -- Translating from de Bruijn to names results in no shadowed variables

  toRaw-NotShadowed : (ctx : Ctx n) (P : Scoped n) → NotShadowed (apply ctx) (toRaw ctx P)
  toRaw-NotShadowed ctx 𝟘 = tt
  toRaw-NotShadowed ctx (ν P ⦃ name ⦄) = fresh-∉ name ctx , (toRaw-NotShadowed (_ ∷ ctx) P)
  toRaw-NotShadowed ctx (P ∥ Q) = toRaw-NotShadowed ctx P , toRaw-NotShadowed ctx Q
  toRaw-NotShadowed ctx ((x ⦅⦆ P) ⦃ name ⦄) = fresh-∉ name ctx , toRaw-NotShadowed (name ∷ ctx) P
  toRaw-NotShadowed ctx (x ⟨ y ⟩ P) = toRaw-NotShadowed ctx P

  -- Translating from de Bruijn to names and back results in the same process modulo name hints

  data _α-≡_ {n} : Scoped n → Scoped n → Set where
    inaction : 𝟘 α-≡ 𝟘
    scope    : P α-≡ Q → ν P ⦃ namex ⦄ α-≡ ν Q ⦃ namey ⦄
    comp     : P α-≡ Q → R α-≡ S → (P ∥ R) α-≡ (Q ∥ S)
    input    : P α-≡ Q → (x ⦅⦆ P) ⦃ namex ⦄ α-≡ (x ⦅⦆ Q) ⦃ namey ⦄
    output   : P α-≡ Q → (x ⟨ y ⟩ P) α-≡ (x ⟨ y ⟩ Q)

  fromRaw∘toRaw : (ctx : Ctx n) (P : Scoped n)
                → fromRaw' (apply ctx) (toRaw ctx P) (toRaw-WellScoped ctx P) α-≡ P
  fromRaw∘toRaw ctx 𝟘 = inaction
  fromRaw∘toRaw ctx (ν P ⦃ name ⦄) =
    scope (fromRaw∘toRaw (name ∷ ctx) P)
  fromRaw∘toRaw ctx (P ∥ Q) =
    comp (fromRaw∘toRaw ctx P) (fromRaw∘toRaw ctx Q)
  fromRaw∘toRaw ctx ((x ⦅⦆ P) ⦃ name ⦄)
    rewrite fromName∘toName x (apply ctx) =
    input (fromRaw∘toRaw (name ∷ ctx) P)
  fromRaw∘toRaw ctx (x ⟨ y ⟩ P)
    rewrite fromName∘toName x (apply ctx) | fromName∘toName y (apply ctx) =
    output (fromRaw∘toRaw ctx P)


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
             → ⦅ν x ⦆ P α[ ks ↦ vs ]≡ ⦅ν y ⦆ Q
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

  toRaw∘fromRaw : (ctx : Ctx n) (P : Raw) (wsP : WellScoped ctx P)
                → toRaw ctx (fromRaw' ctx P wsP) α[ apply ctx ↦ ctx ]≡ P
  toRaw∘fromRaw ctx 𝟘 wsP = inaction
  toRaw∘fromRaw ctx (⦅ν x ⦆ P) wsP
    = scope (toRaw∘fromRaw (x ∷ ctx) P wsP)
  toRaw∘fromRaw ctx (P ∥ Q) (wsP , wsQ)
    = comp (toRaw∘fromRaw ctx P wsP)
           (toRaw∘fromRaw ctx Q wsQ)
  toRaw∘fromRaw ctx (x ⦅ y ⦆ P) (x∈ctx , wsP)
    = input (_ , refl , toName∘fromName x∈ctx)
            (toRaw∘fromRaw (y ∷ ctx) P wsP)
  toRaw∘fromRaw ctx (x ⟨ y ⟩ P) (x∈ctx , y∈ctx , wsP)
    = output (_ , refl , toName∘fromName x∈ctx)
             (_ , refl , toName∘fromName y∈ctx)
             (toRaw∘fromRaw ctx P wsP)
