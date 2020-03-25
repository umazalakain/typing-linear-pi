open import Data.Unit
open import Data.Maybe

module PiCalculus.Syntax where

-- Due to Guillaume Allais
-- https://github.com/gallais/potpourri/blob/master/agda/poc/AllLambdas.agda

record Parameters : Set₁ where
  field Ctx  : Set
        Bnd  : Set
        Var  : Ctx → Set
        _,-_ : Ctx → Bnd → Ctx

module Syntax (P : Parameters) where
  infix 20 _∥_
  infixr 15 ⦅new_⦆_
  infixr 9 _⦅_⦆_
  infixr 9 _⟨_⟩_

  open Parameters P

  data Process (Γ : Ctx) : Set where
    𝟘       : Process Γ
    ⦅new_⦆_ : (b : Bnd) → Process (Γ ,- b) → Process Γ
    _∥_     : Process Γ → Process Γ → Process Γ
    _⦅_⦆_   : Var Γ → (b : Bnd) → Process (Γ ,- b) → Process Γ
    _⟨_⟩_   : Var Γ → Var Γ → Process Γ → Process Γ

module Raw where

  open import Data.String.Base

  private
    p : Parameters
    p = record
      { Ctx  = ⊤
      ; Bnd  = String
      ; Var  = λ _ → String
      ; _,-_ = _
      }

  module Raw = Syntax.Process p
  Raw = Syntax.Process p


module Scoped where

  open import Data.Nat.Base
  open import Data.Fin.Base

  private
    p : Parameters
    p = record
      { Ctx  = ℕ
      ; Bnd  = ⊤
      ; Var  = Fin
      ; _,-_ = λ n _ → suc n
      }

  module Scoped = Syntax.Process p
  Scoped = Syntax.Process p

  pattern new_ P = Syntax.⦅new_⦆_ _ P
  pattern _⦅⦆_ x P = Syntax._⦅_⦆_ x _ P

module Conversion where
  open Syntax
  open Raw
  open Scoped

  open import Data.Nat using (ℕ)
  open import Data.Vec using (Vec; []; _∷_)
  open import Data.String using (String)
  open import Relation.Nullary using (yes; no)
  open import Data.Vec.Relation.Unary.Any using (index)

  import Data.Vec.Membership.DecPropositional as DecPropositional
  import Data.String.Properties as Stringₚ
  _∈?_ = DecPropositional._∈?_ Stringₚ._≟_

  raw→scoped : ∀ {n} → Vec String n → Raw tt → Maybe (Scoped n)
  raw→scoped ctx 𝟘                              = just 𝟘
  raw→scoped ctx (⦅new b ⦆ P)                   = do P' ← raw→scoped (b ∷ ctx) P
                                                     just (new P')
  raw→scoped ctx (P ∥ Q)                        = do P' ← raw→scoped ctx P
                                                     Q' ← raw→scoped ctx Q
                                                     just (P' ∥ Q')
  raw→scoped ctx (x ⦅ b ⦆ P)  with x ∈? ctx
  raw→scoped ctx (x ⦅ b ⦆ P)  | yes p           = do P' ← raw→scoped (b ∷ ctx) P
                                                     just (index p ⦅⦆ P')
  raw→scoped ctx (x ⦅ b ⦆ P)  | _               = nothing
  raw→scoped ctx (x ⟨ y ⟩ P)  with x ∈? ctx | y ∈? ctx
  raw→scoped ctx (x ⟨ y ⟩ P)  | yes xp | yes yp = do P' ← raw→scoped ctx P
                                                     just (index xp ⟨ index yp ⟩ P')
  raw→scoped ctx (x ⟨ y ⟩ P)  | _      | _      = nothing
