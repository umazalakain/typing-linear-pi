open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (#_; zero; suc)
open import Data.Product using (_,_)
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Relation.Unary.All using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Level as L

open import PiCalculus.Syntax
open Syntax
open Raw
open Scoped
open Conversion
open import PiCalculus.Semantics
open import PiCalculus.LinearTypeSystem
open import PiCalculus.LinearTypeSystem.OmegaNat

module PiCalculus.Examples where

variable
  n : ℕ

raw : Raw tt
raw = ⦅new "x"⦆ (("x" ⦅ "b" ⦆ 𝟘) ∥ (+[ "a" ] ("x" ⟨ "a" ⟩ 𝟘)))

scoped : Scoped 0
scoped = new (((# 0) ⦅⦆ 𝟘) ∥ (+[] ((# 1) ⟨ # 0 ⟩ 𝟘)))

_ : raw→scoped raw ≡ just scoped
_ = refl

channel-over-channel₀ : Raw tt
channel-over-channel₀ = ⦅new "x"⦆
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ (⦅new "z"⦆ (+[ "y" ] ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘))))

channel-over-channel₁ : Raw tt
channel-over-channel₁ = ⦅new "x"⦆ ⦅new "z"⦆
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ (+[ "y" ] ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘)))

channel-over-channel₂ : Raw tt
channel-over-channel₂ = ⦅new "x"⦆ ⦅new "z"⦆ +[ "y" ]
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₃ : Raw tt
channel-over-channel₃ = ⦅new "z"⦆ ⦅new "x"⦆ +[ "y" ]
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₄ : Raw tt
channel-over-channel₄ = ⦅new "z"⦆ +[ "y" ] ⦅new "x"⦆
                        ( ("x" ⦅ "r" ⦆ "r" ⦅ "p" ⦆ 𝟘)
                        ∥ ("x" ⟨ "z" ⟩ "z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₅ : Raw tt
channel-over-channel₅ = ⦅new "z"⦆ +[ "y" ] ⦅new "x"⦆
                        ( ("z" ⦅ "p" ⦆ 𝟘)
                        ∥ ("z" ⟨ "y" ⟩ 𝟘))

channel-over-channel₆ : Raw tt
channel-over-channel₆ = ⦅new "z"⦆ +[ "y" ] ⦅new "x"⦆
                        (𝟘 ∥ 𝟘)

channel-over-channel₇ : Raw tt
channel-over-channel₇ = ⦅new "z"⦆ +[ "y" ] ⦅new "x"⦆ 𝟘

channel-over-channel₈ : Raw tt
channel-over-channel₈ = ⦅new "z"⦆ +[ "y" ] 𝟘

channel-over-channel₉ : Raw tt
channel-over-channel₉ = ⦅new "z"⦆ 𝟘

channel-over-channel₁₀ : Raw tt
channel-over-channel₁₀ = 𝟘

_≅raw≅_ : Raw tt → Raw tt → Set
P ≅raw≅ Q with raw→scoped P | raw→scoped Q
(P ≅raw≅ Q) | just sP | just sQ = sP ≅ sQ
(P ≅raw≅ Q) | _       | _       = ⊤

_=raw⇒_ : Raw tt → Raw tt → Set
P =raw⇒ Q with raw→scoped P | raw→scoped Q
(P =raw⇒ Q) | just sP | just sQ = sP =[ nothing ]⇒ sQ
(P =raw⇒ Q) | _       | _       = ⊤

_ : channel-over-channel₀ ≅raw≅ channel-over-channel₁
_ = new-cong (cong-symm (scope-ext ((λ ()) , (λ ()) , tt)))

_ : channel-over-channel₁ ≅raw≅ channel-over-channel₂
_ = new-cong (new-cong (cong-symm (base-ext ((λ ()) , (λ ()) , tt))))

_ : channel-over-channel₂ ≅raw≅ channel-over-channel₃
_ = scope-scope-comm

_ : channel-over-channel₃ ≅raw≅ channel-over-channel₄
_ = new-cong scope-base-comm

_ : channel-over-channel₄ =raw⇒ channel-over-channel₅
_ = res (base (res (comm)))

_ : channel-over-channel₅ =raw⇒ channel-over-channel₆
_ = res (base (res comm))

_ : channel-over-channel₆ ≅raw≅ channel-over-channel₇
_ = new-cong (base-cong (new-cong comp-end))

_ : channel-over-channel₇ ≅raw≅ channel-over-channel₈
_ = new-cong (base-cong scope-end)

_ : channel-over-channel₈ ≅raw≅ channel-over-channel₉
_ = new-cong base-end

_ : channel-over-channel₉ ≅raw≅ channel-over-channel₁₀
_ = scope-end

raw⊢_ : Raw tt → Set
raw⊢ P with raw→scoped P
(raw⊢ P) | just P' = [] w tt ⊢ P'
(raw⊢ P) | nothing = L.Lift _ ⊤

_ : raw⊢ (⦅new "x" ⦆ (+[ "a" ] ("x" ⟨ "a" ⟩ 𝟘)) ∥ ("x" ⦅ "b" ⦆ 𝟘))
_ = chan B[ 0 ] [] 1∙
    (comp
    (base (send  (suc zero) zero  end))
    (recv zero end))

_ : raw⊢ channel-over-channel₀
_ = chan C[ B[ 0 ] w [] ] (0∙ ↑ 1∙ ↓) 1∙ (comp
         (recv zero
               (recv zero end))
         (chan B[ 0 ] [] 1∙ (base
               (send (suc (suc zero)) (suc zero)
                     (send (suc zero) zero end)))))

_ : raw⊢ channel-over-channel₀
_ = chan C[ B[ 0 ] w [] ] (0∙ ↑ 1∙ ↓) ω∙ (comp
         (recv zero
               (recv zero end))
         (chan B[ 0 ] [] 1∙ (base
               (send (suc (suc zero)) (suc zero)
                     (send (suc zero) zero end)))))
