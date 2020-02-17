open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl; subst; trans; cong)
open import Function using (_∘_)

import Data.Nat as ℕ
import Data.Product as Product
import Data.Product.Properties as Productₚ
import Data.Vec as Vec
import Data.Vec.Relation.Unary.All as All
import Data.Fin as Fin

open ℕ using (ℕ; zero; suc)
open Product using (Σ; Σ-syntax; _×_; _,_; proj₂; proj₁)
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

_⊎_ : {ss : Shapes n} {cs : Cards ss} → Mults cs → Mults cs → Mults cs
_⊎_ {ss = []} tt tt = tt
_⊎_ {ss = _ -, _} (Γ , m) (Δ , n) = Γ ⊎ Δ , m +ᵥ n

⊎-idˡ : {ss : Shapes n} {cs : Cards ss} (Γ : Mults cs) → ε ⊎ Γ ≡ Γ
⊎-idˡ {ss = []} tt = refl
⊎-idˡ {ss = _ -, _} (Γ , m) rewrite ⊎-idˡ Γ | +ᵥ-idˡ m = refl

⊎-idʳ : {ss : Shapes n} {cs : Cards ss} (Γ : Mults cs) → Γ ⊎ ε ≡ Γ
⊎-idʳ {ss = []} tt = refl
⊎-idʳ {ss = _ -, _} (Γ , m) rewrite ⊎-idʳ Γ | +ᵥ-idʳ m = refl

⊎-comm : {ss : Shapes n} {cs : Cards ss} (Γ Δ : Mults cs) → Γ ⊎ Δ ≡ Δ ⊎ Γ
⊎-comm {ss = []} tt tt = refl
⊎-comm {ss = _ -, _} (Γ , m) (Δ , n) rewrite ⊎-comm Γ Δ | +ᵥ-comm m n = refl

⊎-assoc : {ss : Shapes n} {cs : Cards ss} (Γ Δ Ξ : Mults cs) → (Γ ⊎ Δ) ⊎ Ξ ≡ Γ ⊎ (Δ ⊎ Ξ)
⊎-assoc {ss = []} tt tt tt = refl
⊎-assoc {ss = _ -, _} (Γ , m) (Δ , n) (Ξ , l) rewrite ⊎-assoc Γ Δ Ξ | +ᵥ-assoc m n l = refl

⊎-cancelˡ-≡ : {ss : Shapes n} {cs : Cards ss} {Γ Δ Ξ : Mults cs} → Γ ⊎ Δ ≡ Γ ⊎ Ξ → Δ ≡ Ξ
⊎-cancelˡ-≡ {ss = []} {tt} {tt} {tt} _ = refl
⊎-cancelˡ-≡ {ss = _ -, _} {_ , _} {_ , _} {_ , _} eq
  rewrite +ᵥ-cancelˡ-≡ (Productₚ.,-injectiveʳ eq)
  | ⊎-cancelˡ-≡ (Productₚ.,-injectiveˡ eq)
  = refl

_⊆_ : {ss : Shapes n} {cs : Cards ss} → Mults cs → Mults cs → Set
ϕ ⊆ Γ = Σ[ Δ ∈ _ ] ϕ ⊎ Δ ≡ Γ

⊆-refl : {ss : Shapes n} {cs : Cards ss} {Γ : Mults cs} → Γ ⊆ Γ
⊆-refl = ε , ⊎-idʳ _

⊆-trans : {ss : Shapes n} {cs : Cards ss} {Γ Ξ Θ : Mults cs} → Γ ⊆ Ξ → Ξ ⊆ Θ → Γ ⊆ Θ
⊆-trans (Δ₁ , refl) (Δ₂ , refl) = _ , sym (⊎-assoc _ _ _)

⊆-tail : {ss : Shapes n} {cs : Cards ss} {Γ Δ : Mults cs}
       → {s : Shape} {c : Card s} {m l : Mult s c}
       → _⊆_ {ss = _ -, s} (Δ , m) (Γ , l) → Δ ⊆ Γ
⊆-tail = Product.map proj₁ Productₚ.,-injectiveˡ

⊆-⊎ˡ : {ss : Shapes n} {cs : Cards ss} {Γ Ξ : Mults cs} (Δ : Mults cs) → Γ ⊆ Ξ → Γ ⊆ (Δ ⊎ Ξ)
⊆-⊎ˡ Δ (diff , refl) = Δ ⊎ diff , trans (⊎-comm _ _) (trans (⊎-assoc _ _ _) (cong (_ ⊎_) (⊎-comm _ _)))

∋-⊆ : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
    → {s : Shape} {c : Card s} {t : Type s} {m : Mult s c}
    → γ w Γ ∋ t w m ⊠ Δ → Δ ⊆ Γ
∋-⊆ zero = (ε , _) , _,_ & ⊎-idʳ _ ⊗ refl
∋-⊆ (suc ⊢P) with ∋-⊆ ⊢P
∋-⊆ (suc ⊢P) | Γ , refl = (Γ , replicate 0∙) , _,_ & refl ⊗ +ᵥ-idʳ _

⊢-⊆ : {ss : Shapes n} {cs : Cards ss} {γ : Types ss} {Γ Δ : Mults cs}
    → γ w Γ ⊢ P ⊠ Δ → Δ ⊆ Γ
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
