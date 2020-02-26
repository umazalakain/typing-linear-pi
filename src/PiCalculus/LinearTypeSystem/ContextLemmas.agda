open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl; subst; trans; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitness)
open import Function using (_∘_)

import Data.Unit as Unit
import Data.Nat as ℕ
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
import Data.Fin as Fin

open Unit using (⊤; tt)
open ℕ using (ℕ; zero; suc)
open Product using (∃-syntax; _×_; _,_; proj₂; proj₁)
open Vec using (Vec; []; _∷_)
open All using (All; []; _∷_)
open Fin using (Fin ; zero ; suc)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import PiCalculus.Function
import PiCalculus.Syntax
open PiCalculus.Syntax.Scoped
open import PiCalculus.Quantifiers

module PiCalculus.LinearTypeSystem.ContextLemmas (Ω : Quantifiers) where
open Quantifiers Ω
open import PiCalculus.LinearTypeSystem Ω

private
  variable
    n : ℕ
    P Q : Scoped n

_≔_⊎_ : {ss : Shapes n} {cs : Cards ss} → Mults cs → Mults cs → Mults cs → Set
_≔_⊎_ {ss = []} tt tt tt = ⊤
_≔_⊎_ {ss = _ -, _} (Γ , xs) (Δ , ys) (Ξ , zs) = Γ ≔ Δ ⊎ Ξ × xs ≔ ys ∙ᵥ zs

⊎-compute : {ss : Shapes n} {cs : Cards ss} (Δ Ξ : Mults cs) → Dec (∃[ Γ ] (Γ ≔ Δ ⊎ Ξ))
⊎-compute {ss = []} tt tt = yes (tt , tt)
⊎-compute {ss = _ -, _} (Δ , ys) (Ξ , zs) with ⊎-compute Δ Ξ | ∙ᵥ-compute ys zs
...                                       | yes (_ , ps)     | yes (_ , p) = yes ((_ , _) , (ps , p))
...                                       | yes (_ , ps)     | no ¬p       = no λ {((_ , _) , (_ , p)) → ¬p (_ , p)}
...                                       | no ¬ps           | _           = no λ {((_ , _) , (ps , _)) → ¬ps (_ , ps)}

⊎-idˡ : {ss : Shapes n} {cs : Cards ss} (Γ : Mults cs) → Γ ≔ ε ⊎ Γ
⊎-idˡ {ss = []} tt = tt
⊎-idˡ {ss = _ -, _} (Γ , xs) = ⊎-idˡ Γ , ∙ᵥ-idˡ xs

⊎-unique : {ss : Shapes n} {cs : Cards ss} {Γ Γ' Δ Ξ  : Mults cs} → Γ' ≔ Δ ⊎ Ξ → Γ ≔ Δ ⊎ Ξ → Γ' ≡ Γ
⊎-unique {ss = []} tt tt = refl
⊎-unique {ss = _ -, _} {Γ = _ , _} {Γ' = _ , _} (Γ'≔ , xs'≔) (Γ≔ , xs≔)
  rewrite ⊎-unique Γ'≔ Γ≔ | ∙ᵥ-unique xs'≔ xs≔ = refl

⊎-cancelˡ : {ss : Shapes n} {cs : Cards ss} {Γ Δ Δ' Ξ  : Mults cs} → Γ ≔ Δ' ⊎ Ξ → Γ ≔ Δ ⊎ Ξ → Δ' ≡ Δ
⊎-cancelˡ {ss = []} tt tt = refl
⊎-cancelˡ {ss = _ -, _} {Δ = _ , _} {Δ' = _ , _} (Δ'≔ , ys'≔) (Δ≔ , ys≔)
  rewrite ⊎-cancelˡ Δ'≔ Δ≔ | ∙ᵥ-cancelˡ ys'≔ ys≔ = refl

⊎-comm : {ss : Shapes n} {cs : Cards ss} {Γ Δ Ξ : Mults cs} → Γ ≔ Δ ⊎ Ξ → Γ ≔ Ξ ⊎ Δ
⊎-comm {ss = []} tt = tt
⊎-comm {ss = _ -, _} (Γ≔ , xs≔) = ⊎-comm Γ≔ , ∙ᵥ-comm xs≔

⊎-assoc : {ss : Shapes n} {cs : Cards ss} {Γₘ Γₗ Γᵣ Γₗₗ Γₗᵣ : Mults cs}
        → Γₘ ≔ Γₗ ⊎ Γᵣ → Γₗ ≔ Γₗₗ ⊎ Γₗᵣ → ∃[ Γᵣ' ] (Γₘ ≔ Γₗₗ ⊎ Γᵣ' × Γᵣ' ≔ Γₗᵣ ⊎ Γᵣ)
⊎-assoc {ss = []} tt tt = tt , tt , tt
⊎-assoc {ss = _ -, _} (Γₘ≔ , xsₘ≔) (Γₗ≔ , xsₗ≔) with ⊎-assoc Γₘ≔ Γₗ≔ | ∙ᵥ-assoc xsₘ≔ xsₗ≔
... | (_ , Γₘ'≔ , Γᵣ'≔)  | (_ , xsₘ'≔ , xsᵣ'≔) = _ , ((Γₘ'≔ , xsₘ'≔) , (Γᵣ'≔ , xsᵣ'≔))

⊎-idʳ : {ss : Shapes n} {cs : Cards ss} (Γ : Mults cs) → Γ ≔ Γ ⊎ ε
⊎-idʳ Γ = ⊎-comm (⊎-idˡ Γ)

∋-⊎ : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Ξ : Mults cs}
    → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
    → γ w Γ ∋ t w m ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
∋-⊎ (zero {check = check}) = (ε , _) , ((⊎-idˡ _) , proj₂ (toWitness check))
∋-⊎ (suc i) with ∋-⊎ i
∋-⊎ (suc i) | (Δ , Γ≔) = (Δ , replicate 0∙) , Γ≔ , (∙ᵥ-idˡ _)

⊢-⊎ : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Ξ : Mults cs}
    → γ w Γ ⊢ P ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
⊢-⊎ end = ε , ⊎-idˡ _
⊢-⊎ (base ⊢P) = let (_ , Γ≔ , _) = ⊢-⊎ ⊢P in _ , Γ≔
⊢-⊎ (chan t m μ ⊢P) = let (_ , Γ≔ , _) = ⊢-⊎ ⊢P in _ , Γ≔
⊢-⊎ (recv x ⊢P) = let (_ , x≔) = ∋-⊎ x; (_ , Γ≔ , _) = ⊢-⊎ ⊢P in _ , {!!}
⊢-⊎ (send x y ⊢P) = let (_ , x≔) = ∋-⊎ x; (_ , y≔) = ∋-⊎ y; (_ , ⊢P≔) = ⊢-⊎ ⊢P in _ , ⊎-comm {!!}
⊢-⊎ (comp ⊢P ⊢Q) = let (_ , Γ≔) = ⊢-⊎ ⊢P
                       (_ , Θ≔) = ⊢-⊎ ⊢Q
                       (_ , R≔ , _) = ⊎-assoc (⊎-comm Γ≔) (⊎-comm Θ≔)
                    in _ , ⊎-comm R≔

{-

⊢-⊆ end = ⊆-refl
⊢-⊆ (base ⊢P) = ⊆-tail {s = < 0 & _ , [] >} (⊢-⊆ ⊢P)
⊢-⊆ (chan {s = s} t m μ ⊢P) = ⊆-tail {s = < 2 & _ , s ∷ [] >} (⊢-⊆ ⊢P)
⊢-⊆ (recv {s = s} x ⊢P) = ⊆-trans (⊆-tail {s = s} (⊢-⊆ ⊢P) ) (∋-⊆ x)
⊢-⊆ (send x y ⊢P) = ⊆-trans (⊢-⊆ ⊢P) (⊆-trans (∋-⊆ y) (∋-⊆ x))
⊢-⊆ (comp ⊢P ⊢Q) = ⊆-trans (⊢-⊆ ⊢Q) (⊢-⊆ ⊢P)

get-shape : Shapes n → Fin n → Shape
get-shape = Vec.lookup

get-type : {ss : Shapes n} → Types ss → (i : Fin n) → Type (get-shape ss i)
get-type {ss = _ -, _} (ts -, t) zero = t
get-type {ss = _ -, _} (ts -, t) (suc i) = get-type ts i

get-card : {ss : Shapes n} → Cards ss → (i : Fin n) → Card (get-shape ss i)
get-card {ss = _ -, _} (cs , c) zero = c
get-card {ss = _ -, _} (cs , c) (suc i) = get-card cs i

get-mult : {ss : Shapes n} {cs : Cards ss} → Mults cs → (i : Fin n)
         → Mult (get-shape ss i) (get-card cs i)
get-mult {ss = _ -, _} (ms , m) zero = m
get-mult {ss = _ -, _} (ms , m) (suc i) = get-mult ms i

update-mult : {ss : Shapes n} {cs : Cards ss}
            → (i : Fin n)
            → Mult (get-shape ss i) (get-card cs i)
            → Mults cs
            → Mults cs
update-mult {ss = _ -, _} zero m' (ms , m) = ms , m'
update-mult {ss = _ -, _} (suc i) m' (ms , m) = update-mult i m' ms , m

fromFin : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ : Mults cs}
        → (i : Fin n) {m : Mult (get-shape ss i) (get-card cs i)}
        → γ w update-mult i (get-mult Γ i +ᵥ m) Γ ∋ get-type γ i w m ⊠ Γ
fromFin {ss = _ -, _} {γ = _ -, _} zero = zero
fromFin {ss = _ -, _} {γ = _ -, _} (suc i) = suc (fromFin i)
-}
