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
    γ : PreCtx n
    i : I
    t : Type
    P Q : Scoped n

_≔_⊎_ : Ctx γ → Ctx γ → Ctx γ → Set
_≔_⊎_ [] [] [] = ⊤
_≔_⊎_ (Γ -, xs) (Δ -, ys) (Ξ -, zs) = Γ ≔ Δ ⊎ Ξ × xs ≔ ys ∙ᵥ zs

⊎-compute : (Δ Ξ : Ctx γ) → Dec (∃[ Γ ] (Γ ≔ Δ ⊎ Ξ))
⊎-compute [] [] = yes ([] , tt)
⊎-compute (Δ -, ys) (Ξ -, zs) with ⊎-compute Δ Ξ | ∙ᵥ-compute ys zs
... | yes (_ , ps)     | yes (_ , p) = yes ((_ -, _) , (ps , p))
... | yes (_ , ps)     | no ¬p       = no λ {((_ -, _) , (_ , p)) → ¬p (_ , p)}
... | no ¬ps           | _           = no λ {((_ -, _) , (ps , _)) → ¬ps (_ , ps)}

⊎-idˡ : (Γ : Ctx γ) → Γ ≔ ε ⊎ Γ
⊎-idˡ [] = tt
⊎-idˡ (Γ -, xs) = ⊎-idˡ Γ , ∙ᵥ-idˡ xs

⊎-unique : {Γ Γ' Δ Ξ  : Ctx γ} → Γ' ≔ Δ ⊎ Ξ → Γ ≔ Δ ⊎ Ξ → Γ' ≡ Γ
⊎-unique {Γ = []} {[]} {[]} {[]} tt tt = refl
⊎-unique {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} (Γ'≔ , xs'≔) (Γ≔ , xs≔)
  rewrite ⊎-unique Γ'≔ Γ≔ | ∙ᵥ-unique xs'≔ xs≔ = refl

⊎-cancelˡ : {Γ Δ Δ' Ξ  : Ctx γ} → Γ ≔ Δ' ⊎ Ξ → Γ ≔ Δ ⊎ Ξ → Δ' ≡ Δ
⊎-cancelˡ {Γ = []} {[]} {[]} {[]} tt tt = refl
⊎-cancelˡ {Γ = _ -, _} {_ -, _} {_ -, _} {_ -, _} (Δ'≔ , ys'≔) (Δ≔ , ys≔)
  rewrite ⊎-cancelˡ Δ'≔ Δ≔ | ∙ᵥ-cancelˡ ys'≔ ys≔ = refl

⊎-comm : {Γ Δ Ξ : Ctx γ} → Γ ≔ Δ ⊎ Ξ → Γ ≔ Ξ ⊎ Δ
⊎-comm {Γ = []} {[]} {[]} tt = tt
⊎-comm {Γ = _ -, _} {_ -, _} {_ -, _} (Γ≔ , xs≔) = ⊎-comm Γ≔ , ∙ᵥ-comm xs≔

⊎-assoc : {Γₘ Γₗ Γᵣ Γₗₗ Γₗᵣ : Ctx γ}
        → Γₘ ≔ Γₗ ⊎ Γᵣ → Γₗ ≔ Γₗₗ ⊎ Γₗᵣ → ∃[ Γᵣ' ] (Γₘ ≔ Γₗₗ ⊎ Γᵣ' × Γᵣ' ≔ Γₗᵣ ⊎ Γᵣ)
⊎-assoc {Γₘ = []} {[]} {[]} {[]} {[]}  tt tt = [] , tt , tt
⊎-assoc {Γₘ = _ -, _} {_ -, _} {_ -, _} {_ -, _} {_ -, _} (Γₘ≔ , xsₘ≔) (Γₗ≔ , xsₗ≔) with ⊎-assoc Γₘ≔ Γₗ≔ | ∙ᵥ-assoc xsₘ≔ xsₗ≔
... | (_ , Γₘ'≔ , Γᵣ'≔)  | (_ , xsₘ'≔ , xsᵣ'≔) = _ , ((Γₘ'≔ , xsₘ'≔) , (Γᵣ'≔ , xsᵣ'≔))

⊎-trans : {m l r rl rr : Ctx γ}
        → (t : m ≔ l ⊎ r) → (b : r ≔ rl ⊎ rr)
        → m ≔ proj₁ (⊎-assoc (⊎-comm t) (⊎-comm b)) ⊎ rr
⊎-trans t b = ⊎-comm (proj₁ (proj₂ (⊎-assoc (⊎-comm t) (⊎-comm b))))

⊎-comp : {γ : PreCtx n} {Γ Δₗ Δᵣ Δ Ξ Θ : Ctx γ}
       → Γ ≔ Δₗ ⊎ Ξ → Ξ ≔ Δᵣ ⊎ Θ
       → Γ ≔ Δ  ⊎ Θ → Δ ≔ Δₗ ⊎ Δᵣ
⊎-comp l≔ r≔ Γ≔ with ⊎-assoc (⊎-comm l≔) (⊎-comm r≔)
⊎-comp l≔ r≔ Γ≔ | _ , Γ'≔ , R'≔ rewrite ⊎-cancelˡ Γ≔ (⊎-comm Γ'≔) = ⊎-comm R'≔

⊎-tail : {xs ys zs : Ctx (γ -, (i , t))}
       → xs ≔ ys ⊎ zs → All.tail xs ≔ All.tail ys ⊎ All.tail zs
⊎-tail {xs = _ -, _} {_ -, _} {_ -, _} (tail , _) = tail

⊎-idʳ : (Γ : Ctx γ) → Γ ≔ Γ ⊎ ε
⊎-idʳ Γ = ⊎-comm (⊎-idˡ Γ)

∋-⊎ : {Γ Ξ : Ctx γ} {m : Usage (i , t)}
    → γ w Γ ∋ t w m ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
∋-⊎ (zero {check = check}) = (ε -, _) , ((⊎-idˡ _) , proj₂ (toWitness check))
∋-⊎ (suc i) with ∋-⊎ i
∋-⊎ (suc i) | (Δ , Γ≔) = (Δ -, Vec.replicate 0∙) , Γ≔ , (∙ᵥ-idˡ _)

⊢-⊎ : {Γ Ξ : Ctx γ} → γ w Γ ⊢ P ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
⊢-⊎ end = ε , ⊎-idˡ _
⊢-⊎ (base ⊢P) = let _ , Γ≔ = ⊢-⊎ ⊢P
                 in _ , ⊎-tail Γ≔
⊢-⊎ (chan t m μ ⊢P) = let _ , Γ≔ = ⊢-⊎ ⊢P
                       in _ , ⊎-tail Γ≔
⊢-⊎ (recv x ⊢P) = let _ , x≔ = ∋-⊎ x
                      _ , P≔ = ⊢-⊎ ⊢P
                   in _ , ⊎-trans x≔ (⊎-tail P≔)
⊢-⊎ (send x y ⊢P) = let _ , x≔ = ∋-⊎ x
                        _ , y≔ = ∋-⊎ y
                        _ , P≔ = ⊢-⊎ ⊢P
                     in _ , ⊎-trans (⊎-trans x≔ y≔) P≔
⊢-⊎ (comp ⊢P ⊢Q) = let _ , P≔ = ⊢-⊎ ⊢P
                       _ , Q≔ = ⊢-⊎ ⊢Q
                    in _ , ⊎-trans P≔ Q≔

update-mult : (i : Fin n) → Usage (Vec.lookup γ i) → Ctx γ → Ctx γ
update-mult zero m' (ms -, m) = ms -, m'
update-mult (suc i) m' (ms -, m) = update-mult i m' ms -, m
