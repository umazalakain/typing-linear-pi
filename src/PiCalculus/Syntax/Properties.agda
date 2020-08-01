{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂; curry)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base as Vec using ([]; _∷_; Vec)
open import Data.String.Base as String using (String)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Vec.Relation.Unary.Any as Any using (here; there)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
open import Data.List.Base as List using (List; []; _∷_; [_])
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Vec.Membership.Propositional using (_∈_; _∉_)

import Data.List.Properties as Listₚ
import Data.Nat.Properties as ℕₚ
import Data.Product.Properties as Productₚ
import Data.Vec.Relation.Unary.All.Properties as Allₚ
import Data.Vec.Membership.Propositional.Properties as ∈ₚ
import Data.String.Properties as Stringₚ

open import PiCalculus.Syntax
open Raw
open Scoped
open Conversion

open import PiCalculus.Utils
open AllAcc using ([]; _∷_)

module PiCalculus.Syntax.Properties where

postulate
  -- PR accepted, landing in 2.6.2 https://github.com/agda/agda/pull/4790
  fromList-injective : ∀ a b → String.fromList a ≡ String.fromList b → a ≡ b

module _ where
  private
    variable
      n m : ℕ
      P Q R S : Scoped n
      x y : Fin n
      ys : Vec (Fin n) m
      nx ny : Name
      nsx nsy : Vec Name n

  fromName∘toName : (i : Fin n) (ctx : Ctx n) → Any.index (∈ₚ.∈-lookup i ctx) ≡ i
  fromName∘toName zero (x ∷ ctx) = refl
  fromName∘toName (suc i) (x ∷ ctx) rewrite fromName∘toName i ctx = refl

  toName∘fromName : ∀ {x} {ctx : Ctx n} (x∈ctx : x ∈ ctx) → Vec.lookup ctx (Any.index x∈ctx) ≡ x
  toName∘fromName (here px) = sym px
  toName∘fromName (there x∈ctx) = toName∘fromName x∈ctx

  -- The circum (^) is not a decimal character
  ^∉DECIMALS : '^' ∉ ℕₛ.DECIMALS
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


  -- TODO: rewrite all this
  -- A fresh variable name created from inspecting a context cannot be in that context
  fresh-∉' : ∀ m name (xs : Ctx n) → toString (name , m ℕ.+ (count name xs)) ∉ apply xs
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

  fresh-∉ : ∀ name (xs : Ctx n) → toString (name , count name xs) ∉ apply xs
  fresh-∉ name xs = fresh-∉' zero name xs

  count-++ : ∀ x (xs : Ctx n) (ys : Ctx m) → count x (xs Vec.++ ys) ≡ count x xs ℕ.+ count x ys
  count-++ e [] ys = refl
  count-++ e (x ∷ xs) ys with x Stringₚ.≟ e
  count-++ e (x ∷ xs) ys | yes refl rewrite count-++ e xs ys = refl
  count-++ e (x ∷ xs) ys | no ¬p rewrite count-++ e xs ys = refl

  fresh-∉-++ : ∀ (names : Ctx n) (ctx : Ctx m) → All (_∉ apply ctx) (apply-++ names ctx)
  fresh-∉-++ [] ctx = []
  fresh-∉-++ (name ∷ names) ctx rewrite count-++ name names ctx = fresh-∉' (count name names) name ctx ∷ fresh-∉-++ names ctx

  apply-++-apply : (xs : Ctx n) (ys : Ctx m) → apply-++ xs ys Vec.++ apply ys ≡ apply (xs Vec.++ ys)
  apply-++-apply [] ys = refl
  apply-++-apply (x ∷ xs) ys = cong₂ _∷_ refl (apply-++-apply xs ys)

  -- Translating from de Bruijn to names results in a well-scoped process

  toRaw-WellScoped : (ctx : Ctx n) (P : Scoped n) → WellScoped (apply ctx) (toRaw ctx P)
  toRaw-WellScoped ctx 𝟘 = tt
  toRaw-WellScoped ctx (ν P ⦃ name ⦄) = toRaw-WellScoped (name ∷ ctx) P
  toRaw-WellScoped ctx (P ∥ Q) = toRaw-WellScoped ctx P , toRaw-WellScoped ctx Q
  toRaw-WellScoped {n = n} ctx ((x ⦅ m ⦆ P) ⦃ names ⦄) rewrite apply-++-apply names ctx
    = ∈ₚ.∈-lookup _ _ , toRaw-WellScoped (names Vec.++ ctx) P
  toRaw-WellScoped ctx (x ⟨ ys ⟩ P) = ∈ₚ.∈-lookup _ _ , Allₚ.map⁺ (All.universal (λ _ → ∈ₚ.∈-lookup _ _) ys)  , toRaw-WellScoped ctx P

  -- Translating from de Bruijn to names results in no shadowed variables

  toRaw-NotShadowed : (ctx : Ctx n) (P : Scoped n) → NotShadowed (apply ctx) (toRaw ctx P)
  toRaw-NotShadowed ctx 𝟘 = tt
  toRaw-NotShadowed ctx (ν P ⦃ name ⦄) = fresh-∉ name ctx , (toRaw-NotShadowed (_ ∷ ctx) P)
  toRaw-NotShadowed ctx (P ∥ Q) = toRaw-NotShadowed ctx P , toRaw-NotShadowed ctx Q
  toRaw-NotShadowed {n = n} ctx ((x ⦅ m ⦆ P) ⦃ names ⦄)
    rewrite apply-++-apply names ctx
    = fresh-∉-++ names ctx , toRaw-NotShadowed (names Vec.++ ctx) P
  toRaw-NotShadowed ctx (x ⟨ ys ⟩ P) = toRaw-NotShadowed ctx P

  private
    fromName∘toName-Vec : (ctx : Ctx n) (names : Vec (Fin n) m)
                        → All2Vec.all2vec {P = _∈ apply ctx} Any.index (Allₚ.map⁺ (All.universal (λ z → ∈ₚ.∈-lookup z (apply ctx)) names)) ≡ names
    fromName∘toName-Vec ctx [] = refl
    fromName∘toName-Vec ctx (x ∷ names) = cong₂ _∷_ (fromName∘toName _ _) (fromName∘toName-Vec ctx names)

  -- Translating from de Bruijn to names and back results in the same process modulo name hints
  data _α-≡_ {n} : Scoped n → Scoped n → Set where
    inaction : 𝟘 α-≡ 𝟘
    scope    : P α-≡ Q → ν P ⦃ nx ⦄ α-≡ ν Q ⦃ ny ⦄
    comp     : P α-≡ Q → R α-≡ S → (P ∥ R) α-≡ (Q ∥ S)
    input    : P α-≡ Q → (x ⦅ m ⦆ P) ⦃ nsx ⦄ α-≡ (x ⦅ m ⦆ Q) ⦃ nsy ⦄
    output   : P α-≡ Q → (x ⟨ ys ⟩ P) α-≡ (x ⟨ ys ⟩ Q)

  fromRaw∘toRaw : (ctx : Ctx n) (P : Scoped n)
                → fromRaw' (apply ctx) (toRaw ctx P) (toRaw-WellScoped ctx P) α-≡ P
  fromRaw∘toRaw ctx 𝟘 = inaction
  fromRaw∘toRaw ctx (ν P ⦃ name ⦄) =
    scope (fromRaw∘toRaw (name ∷ ctx) P)
  fromRaw∘toRaw ctx (P ∥ Q) =
    comp (fromRaw∘toRaw ctx P) (fromRaw∘toRaw ctx Q)
  fromRaw∘toRaw {n = n} ctx ((x ⦅ m ⦆ P) ⦃ names ⦄)
    rewrite apply-++-apply names ctx
    | fromName∘toName x (apply ctx) =
    input (fromRaw∘toRaw (names Vec.++ ctx) P)
  fromRaw∘toRaw ctx (x ⟨ ys ⟩ P)
    rewrite fromName∘toName x (apply ctx)
    | fromName∘toName-Vec ctx ys
    = output (fromRaw∘toRaw ctx P)

module _ where
  private
    variable
      n m : ℕ
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
    input    : {ws zs : Ctx n}
             → (x , y) ∈² (ks , vs)
             → P α[ ws Vec.++ ks ↦ zs Vec.++ vs ]≡ Q
             → x ⦅ ws ⦆ P α[ ks ↦ vs ]≡ y ⦅ zs ⦆ Q
    output   : {ws zs : Ctx n}
             → (x , y) ∈² (ks , vs)
             → Pointwise (curry (_∈² (ks , vs))) ws zs
             → P α[ ks ↦ vs ]≡ Q
               → x ⟨ ws ⟩ P α[ ks ↦ vs ]≡ (y ⟨ zs ⟩ Q)

  -- Translating a well-scoped process to de Bruijn and back results in the same process
  -- modulo alpha renaming, where the new names in `apply isf` map to the old in `ctx`

  toRaw∘fromRaw : (ctx : Ctx n) (P : Raw) (wsP : WellScoped ctx P)
                → toRaw ctx (fromRaw' ctx P wsP) α[ apply ctx ↦ ctx ]≡ P
  toRaw∘fromRaw ctx 𝟘 wsP = inaction
  toRaw∘fromRaw ctx (⦅ν x ⦆ P) wsP
    = scope (toRaw∘fromRaw (x ∷ ctx) P wsP)
  toRaw∘fromRaw ctx (P ∥ Q) (wsP , wsQ) = comp (toRaw∘fromRaw ctx P wsP)
           (toRaw∘fromRaw ctx Q wsQ)
  toRaw∘fromRaw {n = n} ctx (_⦅_⦆_ {n = m} x ys P) (x∈ctx , wsP)
    = input (_ , refl , toName∘fromName x∈ctx)
            (subst (toRaw (ys Vec.++ ctx) (fromRaw' (ys Vec.++ ctx) P wsP) α[_↦ ys Vec.++ ctx ]≡ _)
                   (sym (apply-++-apply ys ctx))
                   (toRaw∘fromRaw (ys Vec.++ ctx) P wsP))
  toRaw∘fromRaw ctx (x ⟨ ys ⟩ P) (x∈ctx , ys∈ctx , wsP)
    = output (_ , refl , toName∘fromName x∈ctx)
             (helper ys∈ctx)
             (toRaw∘fromRaw ctx P wsP)
    where
    helper : {ctx : Ctx n} {ys : Ctx m} → (ys∈ctx : All (_∈ ctx) ys)
           → Pointwise (curry (_∈² (apply ctx , ctx))) (Vec.map (Vec.lookup (apply ctx)) (All2Vec.all2vec Any.index ys∈ctx)) ys
    helper [] = []
    helper (y∈ctx ∷ ys∈ctx) = (_ , refl , toName∘fromName y∈ctx) ∷ (helper ys∈ctx)

