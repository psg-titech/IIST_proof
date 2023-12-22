{-# OPTIONS --guardedness #-}

-- Tested with agda 2.6.4 and agda-stdlib 2.0

module IIST-inf where

open import Data.Maybe.Base using ( Maybe; just; nothing )
open import Data.Product.Base as Prod using ( _×_; _,_; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Binary.Structures using ( IsDecEquivalence )

private
  variable
    A B : Set

Eq : Set → Set
Eq A = IsDecEquivalence {A = A} _≡_

-------------------------------------------------------------------------------
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

-------------------------------------------------------------------------------
-- Fallible Colist

mutual

  data FallibleColist (A : Set) : Set where
    [] : FallibleColist A
    fail : FallibleColist A
    _∷_ : A → ∞FallibleColist A → FallibleColist A

  record ∞FallibleColist (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : FallibleColist A

open ∞FallibleColist

-- η is safe for ∞FallibleColist as in https://agda.readthedocs.io/en/latest/language/coinduction.html#the-eta-pragma
{-# ETA ∞FallibleColist #-}

map : (A → B) → FallibleColist A → FallibleColist B
map f [] = []
map f fail = fail
map f (x ∷ xs) = f x ∷ λ where .force → map f (force xs)

shift : A → FallibleColist A → FallibleColist A
shift x [] = []
shift x fail = x ∷ λ where .force → fail
shift x (y ∷ xs) = x ∷ λ where .force → shift y (force xs)

zip : FallibleColist A → FallibleColist B → FallibleColist (A × B)
zip fail _ = fail
zip _ fail = fail
zip [] _ = []
zip _ [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ λ where .force → zip (force xs) (force ys)

unzipₗ : FallibleColist (A × B) → FallibleColist A
unzipₗ = map proj₁

unzipᵣ : FallibleColist (A × B) → FallibleColist B
unzipᵣ = map proj₂

-------------------------------------------------------------------------------
-- Prefix

mutual

  data _≺_ {A : Set} : FallibleColist A → FallibleColist A → Set where
    [] : ∀ {xs} → [] ≺ xs
    fail : fail ≺ fail
    _∷_ : ∀ x {xs ys} → xs ∞≺ ys → (x ∷ xs) ≺ (x ∷ ys)

  record _∞≺_ (xs ys : ∞FallibleColist A) : Set where
    coinductive
    field
      force : force xs ≺ force ys

open _∞≺_

≺-refl : ∀ {xs : FallibleColist A} → xs ≺ xs
≺-refl {xs = []} = []
≺-refl {xs = fail} = fail
≺-refl {xs = x ∷ xs} = x ∷ λ where .force → ≺-refl

≺-trans : ∀ {xs ys zs : FallibleColist A}
  → xs ≺ ys
  → ys ≺ zs
  → xs ≺ zs
≺-trans [] ys≺zs = []
≺-trans fail fail = fail
≺-trans (x ∷ xs≺ys) (.x ∷ ys≺zs) = x ∷ λ where .force → ≺-trans (force xs≺ys) (force ys≺zs)

shift-≺-∷ : ∀ (x : A) xs → (shift x xs) ≺ (x ∷ delay xs)
shift-≺-∷ x [] = []
shift-≺-∷ x fail = x ∷ λ where .force → fail
shift-≺-∷ x (y ∷ xs) = x ∷ λ where .force → shift-≺-∷ y (force xs)

≺-shift : ∀ (x : A) {xs ys} → xs ≺ ys → shift x xs ≺ shift x ys
≺-shift x [] = []
≺-shift x fail = x ∷ λ where .force → fail
≺-shift x (y ∷ xs≺ys) = x ∷ λ where .force → ≺-shift y (force xs≺ys)

≺-zip : ∀ {xs xs' : FallibleColist A} {ys ys' : FallibleColist B}
  → xs' ≺ xs
  → ys' ≺ ys
  → zip xs' ys' ≺ zip xs ys
≺-zip {xs = []} [] fail = fail
≺-zip {xs = fail} [] fail = fail
≺-zip {xs = _ ∷ _} [] fail = fail
≺-zip [] [] = []
≺-zip [] (_ ∷ _) = []
≺-zip fail ys'≺ys = fail
≺-zip (x ∷ xs'≺xs) [] = []
≺-zip (x ∷ xs'≺xs) fail = fail
≺-zip (x ∷ xs'≺xs) (y ∷ ys'≺ys) = (x , y) ∷ λ where .force → ≺-zip (force xs'≺xs) (force ys'≺ys)

≺-unzipₗ : ∀ {xys' xys : FallibleColist (A × B)}
  → xys' ≺ xys
  → unzipₗ xys' ≺ unzipₗ xys
≺-unzipₗ [] = []
≺-unzipₗ fail = fail
≺-unzipₗ ((x , y) ∷ xys'≺xys) = x ∷ λ where .force → ≺-unzipₗ (force xys'≺xys)

≺-unzipᵣ : ∀ {xys' xys : FallibleColist (A × B)}
  → xys' ≺ xys
  → unzipᵣ xys' ≺ unzipᵣ xys
≺-unzipᵣ [] = []
≺-unzipᵣ fail = fail
≺-unzipᵣ ((x , y) ∷ xys'≺xys) = y ∷ λ where .force → ≺-unzipᵣ (force xys'≺xys)

-------------------------------------------------------------------------------
-- Sequence transformation

ST : Set → Set → Set
ST X Y = FallibleColist X → FallibleColist Y
