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
    invertible₁ : ∀ {x y} → to x ≡ just y → from y ≡ just x
    invertible₂ : ∀ {x y} → from y ≡ just x → to x ≡ just y

  invertible₃ : ∀ {x} → to x ≡ nothing → ∀ {y} → from y ≢ just x
  invertible₃ p q with () ← trans (sym p) (invertible₂ q)

  invertible₄ : ∀ {y} → from y ≡ nothing → ∀ {x} → to x ≢ just y
  invertible₄ p q with () ← trans (sym p) (invertible₁ q)

open _⇌_ public

inv⇌ : A ⇌ B → B ⇌ A
inv⇌ f .to = f .from
inv⇌ f .from = f .to
inv⇌ f .invertible₁ = f .invertible₂
inv⇌ f .invertible₂ = f .invertible₁
