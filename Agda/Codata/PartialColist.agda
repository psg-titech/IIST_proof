{-# OPTIONS --guardedness #-}

module Codata.PartialColist where

open import Data.Product.Base using ( _×_; _,_; proj₁; proj₂ )
open import Data.Nat.Base using ( ℕ; zero; suc )
open import Relation.Binary.Bundles using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans )
open import Relation.Binary.Structures using ( IsEquivalence )

open import Codata.PartialConat as Coℕ⊥ using ( Coℕ⊥; zero; ⊥; suc; force; _⊓_ )

private
  variable
    A B : Set

--------------------------------------------------------------------------------
-- Partial Colist

infixr 5 _∷_

mutual

  data Colist⊥ (A : Set) : Set where
    [] : Colist⊥ A
    ⊥ : Colist⊥ A
    _∷_ : (x : A) (xs : ∞Colist⊥ A) → Colist⊥ A

  record ∞Colist⊥ (A : Set) : Set where
    coinductive
    constructor delay
    field force : Colist⊥ A

open ∞Colist⊥ public

-- η is safe for ∞Colist⊥
{-# ETA ∞Colist⊥ #-}

colength : Colist⊥ A → Coℕ⊥
colength [] = zero
colength ⊥ = ⊥
colength (_ ∷ xs) = suc λ where .force → colength (force xs)

map : (A → B) → Colist⊥ A → Colist⊥ B
map f [] = []
map f ⊥ = ⊥
map f (x ∷ xs) = f x ∷ λ where .force → map f (force xs)

zip : Colist⊥ A → Colist⊥ B → Colist⊥ (A × B)
zip ⊥ _ = ⊥
zip _ ⊥ = ⊥
zip [] _ = []
zip _ [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ λ where .force → zip (force xs) (force ys)

unzipₗ : Colist⊥ (A × B) → Colist⊥ A
unzipₗ = map proj₁

unzipᵣ : Colist⊥ (A × B) → Colist⊥ B
unzipᵣ = map proj₂

colength-map : ∀ (f : A → B) xs → colength (map f xs) Coℕ⊥.≈ colength xs
colength-map f [] = zero
colength-map f ⊥ = ⊥
colength-map f (x ∷ xs) = suc λ where .force → colength-map f (force xs)

colength-zip : ∀ {xs : Colist⊥ A} {ys : Colist⊥ B}
  → colength (zip xs ys) Coℕ⊥.≈ (colength xs ⊓ colength ys)
colength-zip {xs = []} {[]} = zero
colength-zip {xs = []} {⊥} = ⊥
colength-zip {xs = []} {_ ∷ _} = zero
colength-zip {xs = ⊥} {[]} = ⊥
colength-zip {xs = ⊥} {⊥} = ⊥
colength-zip {xs = ⊥} {_ ∷ _} = ⊥
colength-zip {xs = _ ∷ _} {[]} = zero
colength-zip {xs = _ ∷ _} {⊥} = ⊥
colength-zip {xs = x ∷ xs} {y ∷ ys} = suc λ where .force → colength-zip

colength-unzipₗ : ∀ {xs : Colist⊥ (A × B)} → colength (unzipₗ xs) Coℕ⊥.≈ colength xs
colength-unzipₗ = colength-map _ _

colength-unzipᵣ : ∀ {xs : Colist⊥ (A × B)} → colength (unzipᵣ xs) Coℕ⊥.≈ colength xs
colength-unzipᵣ = colength-map _ _

--------------------------------------------------------------------------------
-- Bisimulation

infix 4 _≈_ _∞≈_

mutual

  data _≈_ {A : Set} : Colist⊥ A → Colist⊥ A → Set where
    [] : [] ≈ []
    ⊥ : ⊥ ≈ ⊥
    _∷_ : ∀ x {xs ys} (p : xs ∞≈ ys) → x ∷ xs ≈ x ∷ ys

  record _∞≈_ (xs ys : ∞Colist⊥ A) : Set where
    coinductive
    field force : force xs ≈ force ys

open _∞≈_ public

≈-refl : ∀ {xs : Colist⊥ A} → xs ≈ xs
≈-refl {xs = []} = []
≈-refl {xs = ⊥} = ⊥
≈-refl {xs = x ∷ xs} = x ∷ λ where .force → ≈-refl

≈-sym : ∀ {xs ys : Colist⊥ A} → xs ≈ ys → ys ≈ xs
≈-sym [] = []
≈-sym ⊥ = ⊥
≈-sym (x ∷ p) = x ∷ λ where .force → ≈-sym (force p)

≈-trans : ∀ {xs ys zs : Colist⊥ A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans [] q = q
≈-trans ⊥ q = q
≈-trans (x ∷ p) (.x ∷ q) = x ∷ λ where .force → ≈-trans (force p) (force q)

≈-isEquivalence : ∀ {A} → IsEquivalence {A = Colist⊥ A} _≈_
≈-isEquivalence = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = ≈-trans
  }

≈-setoid : ∀ {A} → Setoid _ _
≈-setoid {A} = record { isEquivalence = ≈-isEquivalence {A} }

≈-cong-map : ∀ {xs xs' : Colist⊥ A} (f : A → B)
  → xs ≈ xs'
  → map f xs ≈ map f xs'
≈-cong-map f [] = []
≈-cong-map f ⊥ = ⊥
≈-cong-map f (x ∷ p) = f x ∷ λ where .force → ≈-cong-map f (force p)

≈-cong-zip : ∀ {xs xs' : Colist⊥ A} {ys ys' : Colist⊥ B}
  → xs ≈ xs'
  → ys ≈ ys'
  → zip xs ys ≈ zip xs' ys'
≈-cong-zip ⊥ _ = ⊥
≈-cong-zip [] ⊥ = ⊥
≈-cong-zip (_ ∷ _) ⊥ = ⊥
≈-cong-zip [] [] = []
≈-cong-zip [] (_ ∷ _) = []
≈-cong-zip (_ ∷ _) [] = []
≈-cong-zip (x ∷ p) (y ∷ q) = (x , y) ∷ λ where .force → ≈-cong-zip (force p) (force q)

≈-cong-unzipₗ : ∀ {xs xs' : Colist⊥ (A × B)} → xs ≈ xs' → unzipₗ xs ≈ unzipₗ xs'
≈-cong-unzipₗ = ≈-cong-map _

≈-cong-unzipᵣ : ∀ {xs xs' : Colist⊥ (A × B)} → xs ≈ xs' → unzipᵣ xs ≈ unzipᵣ xs'
≈-cong-unzipᵣ = ≈-cong-map _

-------------------------------------------------------------------------------
-- Prefix

infix 4 _≺_ _∞≺_

mutual

  data _≺_ {A} : Colist⊥ A → Colist⊥ A → Set where
    [] : ∀ {xs} → [] ≺ xs
    ⊥ : ∀ {xs} → ⊥ ≺ xs
    _∷_ : ∀ x {xs ys} (p : xs ∞≺ ys) → x ∷ xs ≺ x ∷ ys

  record _∞≺_ (xs ys : ∞Colist⊥ A) : Set where
    coinductive
    field force : force xs ≺ force ys

open _∞≺_ public

≺-refl : ∀ {xs : Colist⊥ A} → xs ≺ xs
≺-refl {xs = []} = []
≺-refl {xs = ⊥} = ⊥
≺-refl {xs = x ∷ xs} = x ∷ λ where .force → ≺-refl

≺-trans : ∀ {xs ys zs : Colist⊥ A}
  → xs ≺ ys
  → ys ≺ zs
  → xs ≺ zs
≺-trans [] q = []
≺-trans ⊥ q = ⊥
≺-trans (x ∷ p) (.x ∷ q) = x ∷ λ where .force → ≺-trans (force p) (force q)

≺-cong-zip : ∀ {xs xs' : Colist⊥ A} {ys ys' : Colist⊥ B}
  → xs' ≺ xs
  → ys' ≺ ys
  → zip xs' ys' ≺ zip xs ys
≺-cong-zip {xs = []} [] ⊥ = ⊥
≺-cong-zip {xs = ⊥} [] ⊥ = ⊥
≺-cong-zip {xs = _ ∷ _} [] ⊥ = ⊥
≺-cong-zip [] [] = []
≺-cong-zip [] (_ ∷ _) = []
≺-cong-zip {ys = []} ⊥ [] = ⊥
≺-cong-zip {ys = ⊥} ⊥ [] = ⊥
≺-cong-zip {ys = _ ∷ _} ⊥ [] = ⊥
≺-cong-zip ⊥ ⊥ = ⊥
≺-cong-zip ⊥ (_ ∷ _) = ⊥
≺-cong-zip (x ∷ _) [] = []
≺-cong-zip (x ∷ _) ⊥ = ⊥
≺-cong-zip (x ∷ p) (y ∷ q) = (x , y) ∷ λ where .force → ≺-cong-zip (force p) (force q)

≺-cong-unzipₗ : ∀ {xys' xys : Colist⊥ (A × B)}
  → xys' ≺ xys
  → unzipₗ xys' ≺ unzipₗ xys
≺-cong-unzipₗ [] = []
≺-cong-unzipₗ ⊥ = ⊥
≺-cong-unzipₗ ((x , y) ∷ p) = x ∷ λ where .force → ≺-cong-unzipₗ (force p)

≺-cong-unzipᵣ : ∀ {xys' xys : Colist⊥ (A × B)}
  → xys' ≺ xys
  → unzipᵣ xys' ≺ unzipᵣ xys
≺-cong-unzipᵣ [] = []
≺-cong-unzipᵣ ⊥ = ⊥
≺-cong-unzipᵣ ((x , y) ∷ q) = y ∷ λ where .force → ≺-cong-unzipᵣ (force q)

zip-unzipₗ : ∀ (xs : Colist⊥ A) (ys : Colist⊥ B) → unzipₗ (zip xs ys) ≺ xs
zip-unzipₗ [] [] = []
zip-unzipₗ [] ⊥ = ⊥
zip-unzipₗ [] (x ∷ xs) = []
zip-unzipₗ (⊥) ys = ⊥
zip-unzipₗ (x ∷ xs) [] = []
zip-unzipₗ (x ∷ xs) ⊥ = ⊥
zip-unzipₗ (x ∷ xs) (y ∷ ys) = x ∷ λ where .force → zip-unzipₗ (force xs) (force ys)

zip-unzipᵣ : ∀ (xs : Colist⊥ A) (ys : Colist⊥ B) → unzipᵣ (zip xs ys) ≺ ys
zip-unzipᵣ [] [] = []
zip-unzipᵣ [] ⊥ = ⊥
zip-unzipᵣ [] (x ∷ xs) = []
zip-unzipᵣ (⊥) ys = ⊥
zip-unzipᵣ (x ∷ xs) [] = []
zip-unzipᵣ (x ∷ xs) ⊥ = ⊥
zip-unzipᵣ (x ∷ xs) (y ∷ ys) = y ∷ λ where .force → zip-unzipᵣ (force xs) (force ys)

unzip-zip : ∀ {xys : Colist⊥ (A × B)} → zip (unzipₗ xys) (unzipᵣ xys) ≺ xys
unzip-zip {xys = []} = []
unzip-zip {xys = ⊥} = ⊥
unzip-zip {xys = xy ∷ xys} = xy ∷ λ where .force → unzip-zip
