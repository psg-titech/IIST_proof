{-# OPTIONS --safe --cubical #-}

module IIST.Common where

open import Cubical.Foundations.Everything
open import Cubical.Data.Maybe.Base using ( Maybe; just )
open import Cubical.Data.Nat.Base using ( ℕ )
open import Cubical.Data.Nat.Properties using ( discreteℕ )
open import Cubical.Relation.Nullary.Base using ( Discrete )

private
  variable
    A B : Type

--------------------------------------------------------------------------------
-- Eq typeclass

record Eq (A : Type) : Type where
  field _≟_ : Discrete A
  infix 4 _≟_

open Eq {{...}} public

instance
  eqℕ : Eq ℕ
  _≟_ {{eqℕ}} = discreteℕ

--------------------------------------------------------------------------------
-- Partial function and Partial invertible function

infix 0 _⇀_ _⇌_

_⇀_ : Type → Type → Type
A ⇀ B = A → Maybe B

record _⇌_ (A B : Type) : Type where
  field
    to : A ⇀ B
    from : B ⇀ A
    to→from : ∀ {x y} → to x ≡ just y → from y ≡ just x
    from→to : ∀ {x y} → from y ≡ just x → to x ≡ just y

  inverse : B ⇌ A
  to inverse = from
  from inverse = to
  to→from inverse = from→to
  from→to inverse = to→from

open _⇌_ hiding ( inverse ) public
