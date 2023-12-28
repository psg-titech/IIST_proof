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

  ¬dom[to]→¬cod[from] : ∀ {x} → to x ≡ nothing → ∀ {y} → from y ≢ just x
  ¬dom[to]→¬cod[from] p q with () ← trans (sym p) (from→to q)

  ¬dom[from]→¬cod[to] : ∀ {y} → from y ≡ nothing → ∀ {x} → to x ≢ just y
  ¬dom[from]→¬cod[to] p q with () ← trans (sym p) (to→from q)

open _⇌_ public

inv⇌ : A ⇌ B → B ⇌ A
inv⇌ f .to = f .from
inv⇌ f .from = f .to
inv⇌ f .to→from = f .from→to
inv⇌ f .from→to = f .to→from
