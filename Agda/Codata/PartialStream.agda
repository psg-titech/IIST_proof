{-# OPTIONS --guardedness #-}

module Codata.PartialStream where

open import Data.Product.Base using ( _×_; _,_; proj₁; proj₂ )

private
  variable
    A B : Set

--------------------------------------------------------------------------------
-- Partial Stream

infixr 5 _∷_

mutual

  data Stream⊥ (A : Set) : Set where
    _∷_ : A → ∞Stream⊥ A → Stream⊥ A
    ⊥ : Stream⊥ A

  record ∞Stream⊥ (A : Set) : Set where
    coinductive
    constructor delay
    field force : Stream⊥ A

{-# ETA ∞Stream⊥ #-}

open ∞Stream⊥ public

map : (A → B) → Stream⊥ A → Stream⊥ B
map f (x ∷ xs) = f x ∷ λ where .force → map f (force xs)
map f ⊥ = ⊥

zip : Stream⊥ A → Stream⊥ B → Stream⊥ (A × B)
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ λ where .force → zip (force xs) (force ys)
zip ⊥ _ = ⊥
zip _ ⊥ = ⊥

--------------------------------------------------------------------------------
-- No ⊥

mutual

  data No⊥ {A} : Stream⊥ A → Set where
    _∷_ : ∀ x {xs} (p : ∞No⊥ xs) → No⊥ (x ∷ xs)

  record ∞No⊥ {A} (xs : ∞Stream⊥ A) : Set where
    coinductive
    field force : No⊥ (force xs)

open ∞No⊥ public

no⊥-map⁻¹ : ∀ {f : A → B} {xs} → No⊥ (map f xs) → No⊥ xs
no⊥-map⁻¹ {xs = x ∷ _} (_ ∷ p) = x ∷ λ where .force → no⊥-map⁻¹ (force p)

no⊥-zip⁻¹ₗ : ∀ {xs : Stream⊥ A} {ys : Stream⊥ B}
  → No⊥ (zip xs ys)
  → No⊥ xs
no⊥-zip⁻¹ₗ {xs = x ∷ _} {_ ∷ _} (_ ∷ p) = x ∷ λ where .force → no⊥-zip⁻¹ₗ (force p)

no⊥-zip⁻¹ᵣ : ∀ {xs : Stream⊥ A} {ys : Stream⊥ B}
  → No⊥ (zip xs ys)
  → No⊥ ys
no⊥-zip⁻¹ᵣ {xs = _ ∷ _} {y ∷ _} (_ ∷ p) = y ∷ λ where .force → no⊥-zip⁻¹ᵣ (force p)

--------------------------------------------------------------------------------
-- Bisimulation

infix 4 _≈_ _∞≈_

mutual

  data _≈_ {A} : Stream⊥ A → Stream⊥ A → Set where
    _∷_ : ∀ x {xs ys} (p : xs ∞≈ ys) → x ∷ xs ≈ x ∷ ys
    ⊥ : ⊥ ≈ ⊥

  record _∞≈_ {A} (xs ys : ∞Stream⊥ A) : Set where
    coinductive
    field force : force xs ≈ force ys

open _∞≈_ public

≈-refl : ∀ {xs : Stream⊥ A} → xs ≈ xs
≈-refl {xs = x ∷ xs} = x ∷ λ where .force → ≈-refl
≈-refl {xs = ⊥} = ⊥

≈-sym : ∀ {xs ys : Stream⊥ A} → xs ≈ ys → ys ≈ xs
≈-sym (x ∷ p) = x ∷ λ where .force → ≈-sym (force p)
≈-sym ⊥ = ⊥

≈-trans : ∀ {xs ys zs : Stream⊥ A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans (x ∷ p) (.x ∷ q) = x ∷ λ where .force → ≈-trans (force p) (force q)
≈-trans ⊥ ⊥ = ⊥

≈-cong-map : ∀ {f : A → B} {xs ys} → xs ≈ ys → map f xs ≈ map f ys
≈-cong-map (x ∷ p) = _ ∷ λ where .force → ≈-cong-map (force p)
≈-cong-map ⊥ = ⊥

≈-cong-zip : ∀ {xs xs' : Stream⊥ A} {ys ys' : Stream⊥ B}
  → xs ≈ xs'
  → ys ≈ ys'
  → zip xs ys ≈ zip xs' ys'
≈-cong-zip (x ∷ p) (y ∷ q) = (x , y) ∷ λ where .force → ≈-cong-zip (force p) (force q)
≈-cong-zip (_ ∷ _) ⊥ = ⊥
≈-cong-zip ⊥ _ = ⊥

--------------------------------------------------------------------------------
-- More defined

infix 4 _⊑_ _∞⊑_

mutual

  data _⊑_ {A} : Stream⊥ A → Stream⊥ A → Set where
    _∷_ : ∀ x {xs ys} (p : xs ∞⊑ ys) → x ∷ xs ⊑ x ∷ ys
    ⊥ₗ : ∀ {xs} → ⊥ ⊑ xs

  record _∞⊑_ {A} (xs ys : ∞Stream⊥ A) : Set where
    coinductive
    field force : force xs ⊑ force ys

open _∞⊑_ public

⊑-refl : ∀ {xs : Stream⊥ A} → xs ⊑ xs
⊑-refl {xs = x ∷ xs} = x ∷ λ where .force → ⊑-refl
⊑-refl {xs = ⊥} = ⊥ₗ

⊑-trans : ∀ {xs ys zs : Stream⊥ A} → xs ⊑ ys → ys ⊑ zs → xs ⊑ zs
⊑-trans (x ∷ p) (.x ∷ q) = x ∷ λ where .force → ⊑-trans (force p) (force q)
⊑-trans ⊥ₗ q = ⊥ₗ

⊑-cong-map : ∀ {f : A → B} {xs ys}
  → xs ⊑ ys
  → map f xs ⊑ map f ys
⊑-cong-map (x ∷ p) = _ ∷ λ where .force → ⊑-cong-map (force p)
⊑-cong-map ⊥ₗ = ⊥ₗ

⊑-cong-zip : ∀ {xs xs' : Stream⊥ A} {ys ys' : Stream⊥ B}
  → xs ⊑ xs'
  → ys ⊑ ys'
  → zip xs ys ⊑ zip xs' ys'
⊑-cong-zip (x ∷ p) (y ∷ q) = (x , y) ∷ λ where .force → ⊑-cong-zip (force p) (force q)
⊑-cong-zip ⊥ₗ _ = ⊥ₗ
⊑-cong-zip (_ ∷ _) ⊥ₗ = ⊥ₗ

⊑-zip-unzipₗ : ∀ {xs : Stream⊥ A} {ys : Stream⊥ B}
  → map proj₁ (zip xs ys) ⊑ xs
⊑-zip-unzipₗ {xs = x ∷ xs} {y ∷ ys} = x ∷ λ where .force → ⊑-zip-unzipₗ
⊑-zip-unzipₗ {xs = _ ∷ _} {⊥} = ⊥ₗ
⊑-zip-unzipₗ {xs = ⊥} = ⊥ₗ

⊑-zip-unzipᵣ : ∀ {xs : Stream⊥ A} {ys : Stream⊥ B}
  → map proj₂ (zip xs ys) ⊑ ys
⊑-zip-unzipᵣ {xs = x ∷ xs} {y ∷ ys} = y ∷ λ where .force → ⊑-zip-unzipᵣ
⊑-zip-unzipᵣ {xs = _ ∷ _} {⊥} = ⊥ₗ
⊑-zip-unzipᵣ {xs = ⊥} = ⊥ₗ

⊑-unzip-zip : ∀ {xys : Stream⊥ (A × B)} → zip (map proj₁ xys) (map proj₂ xys) ⊑ xys
⊑-unzip-zip {xys = xy ∷ xys} = xy ∷ λ where .force → ⊑-unzip-zip
⊑-unzip-zip {xys = ⊥} = ⊥ₗ
