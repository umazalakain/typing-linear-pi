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
    is : Vec I n
    γ : PreCtx n
    i i' : I
    t : Type
    P Q : Scoped n

∋-I : {m : Cs i'} {y : Cs i} {Γ Δ : Ctx is}
    → (x : γ w Γ ∋ C[ t w m ] w y ⊠ Δ)
    → i ≡ Vec.lookup is (toFin x)
∋-I zero = refl
∋-I (suc x) = ∋-I x

∋-∙ : {m : Cs i'} {y : Cs i} {Γ Δ : Ctx is}
    → (x : γ w Γ ∋ C[ t w m ] w y ⊠ Δ)
    → ∃[ z ] (All.lookup (toFin x) Γ ≔ cast (∋-I x) y ∙ z)
∋-∙ (zero {check = check}) = _ , proj₂ (toWitness check)
∋-∙ (suc x) = ∋-∙ x

∋-⊎ : {Γ Ξ : Ctx is} {x : Cs i} → γ w Γ ∋ t w x ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
∋-⊎ (zero {check = check}) = (ε -, _) , ((⊎-idˡ _) , proj₂ (toWitness check))
∋-⊎ (suc i) with ∋-⊎ i
∋-⊎ (suc i) | (Δ , Γ≔) = (Δ -, 0∙) , Γ≔ , (∙-idˡ _)

⊢-⊎ : {Γ Ξ : Ctx is} → γ w Γ ⊢ P ⊠ Ξ → ∃[ Δ ] (Γ ≔ Δ ⊎ Ξ)
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

update-mult : (i : Fin n) → Cs (Vec.lookup is i) → Ctx is → Ctx is
update-mult zero m' (ms -, m) = ms -, m'
update-mult (suc i) m' (ms -, m) = update-mult i m' ms -, m
