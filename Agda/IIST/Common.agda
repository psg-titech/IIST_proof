module IIST.Common where

open import Data.Maybe.Base using ( Maybe; just; nothing )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong; sym )
open import Relation.Binary.Structures using ( IsDecEquivalence )
open import Relation.Binary.TypeClasses using ( _≟_ )

private
  variable
    A B : Set

--------------------------------------------------------------------------------
-- Eq typeclass

Eq : Set → Set
Eq A = IsDecEquivalence {A = A} _≡_

--------------------------------------------------------------------------------
-- Partial function and Partial invertible function

infix 0 _⇀_ _⇌_

_⇀_ : Set → Set → Set
A ⇀ B = A → Maybe B

record _⇌_ (A B : Set) : Set where
  field
    to : A ⇀ B
    from : B ⇀ A
    invertible₁ : ∀ {x y} → to x ≡ just y → from y ≡ just x
    invertible₂ : ∀ {x y} → from y ≡ just x → to x ≡ just y

open _⇌_

inv⇌ : A ⇌ B → B ⇌ A
inv⇌ f .to = f .from
inv⇌ f .from = f .to
inv⇌ f .invertible₁ = f .invertible₂
inv⇌ f .invertible₂ = f .invertible₁
