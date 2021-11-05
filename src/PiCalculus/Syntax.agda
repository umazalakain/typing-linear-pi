{-# OPTIONS --safe --without-K #-}

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)

module PiCalculus.Syntax where


infixr 20 _∥_
infixr 15 ν
infixr 10 _⦅⦆_ _⟨_⟩_

private
  variable
    n : ℕ

data Scoped : ℕ → Set where
  𝟘     : Scoped n
  ν     : Scoped (suc n) → Scoped n
  _∥_   : Scoped n → Scoped n → Scoped n
  _⦅⦆_  : Fin n → Scoped (suc n) → Scoped n
  _⟨_⟩_ : Fin n → Fin n → Scoped n → Scoped n
