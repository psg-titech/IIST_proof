module IIST.Common where

open import Data.Maybe.Base using ( Maybe; just; nothing )
open import Relation.Binary.PropositionalEquality using ( _≡_; _≢_; refl; sym; trans )
open import Relation.Binary.Structures using ( IsDecEquivalence )

private
  variable
    A B : Set

--------------------------------------------------------------------------------
-- Eq typeclass

Eq : Set → Set
Eq A = IsDecEquivalence {A = A} _≡_

open import Relation.Binary.TypeClasses using ( _≟_ ) public

--------------------------------------------------------------------------------
-- Partial function and Partial invertible function

infix 0 _⇀_ _⇌_

_⇀_ : Set → Set → Set
A ⇀ B = A → Maybe B

record _⇌_ (A B : Set) : Set where
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
