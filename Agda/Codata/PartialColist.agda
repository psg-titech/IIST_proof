{-# OPTIONS --guardedness #-}

module Codata.PartialColist where

open import Data.Product.Base using ( _×_; _,_; proj₁; proj₂ )
open import Data.Nat.Base using ( ℕ; zero; suc )
open import Data.List.Base using ( List; []; _∷_ )
open import Relation.Binary.Bundles using ( Setoid; Preorder )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans )
open import Relation.Binary.Structures using ( IsEquivalence; IsPreorder )

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

fromList : List A → Colist⊥ A
fromList [] = []
fromList (x ∷ xs) = x ∷ delay (fromList xs)

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

  data _≈_ {A} : (xs ys : Colist⊥ A) → Set where
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

module ≈-Reasoning {A} where
  open import Relation.Binary.Reasoning.Setoid (≈-setoid {A}) public

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

unzip-zip : ∀ {xys : Colist⊥ (A × B)} → zip (unzipₗ xys) (unzipᵣ xys) ≈ xys
unzip-zip {xys = []} = []
unzip-zip {xys = ⊥} = ⊥
unzip-zip {xys = xy ∷ xs} = xy ∷ λ where .force → unzip-zip

zip-⊥ᵣ : ∀ {xs : Colist⊥ A} → zip {A} {B} xs ⊥ ≈ ⊥
zip-⊥ᵣ {xs = []} = ⊥
zip-⊥ᵣ {xs = ⊥} = ⊥
zip-⊥ᵣ {xs = _ ∷ _} = ⊥

-------------------------------------------------------------------------------
-- Prefix

infix 4 _≺_ _≺≺_

data PrefixKind : Set where
  ⊥≺⊥ ⊥≺xs : PrefixKind

mutual

  data Prefix {A} : PrefixKind → Colist⊥ A → Colist⊥ A → Set where
    [] : ∀ {k xs} → Prefix k [] xs
    ⊥ : Prefix ⊥≺⊥ ⊥ ⊥
    ⊥ₗ : ∀ {xs} → Prefix ⊥≺xs ⊥ xs
    _∷_ : ∀ {k} x {xs ys} (p : ∞Prefix k xs ys) → Prefix k (x ∷ xs) (x ∷ ys)

  record ∞Prefix k (xs ys : ∞Colist⊥ A) : Set where
    coinductive
    field force : Prefix k (force xs) (force ys)

open ∞Prefix public

_≺_ _≺≺_ : Colist⊥ A → Colist⊥ A → Set
_≺_ = Prefix ⊥≺⊥
_≺≺_ = Prefix ⊥≺xs

prefix-reflexive : ∀ {k} {xs ys : Colist⊥ A} → xs ≈ ys → Prefix k xs ys
prefix-reflexive [] = []
prefix-reflexive {k = ⊥≺⊥} ⊥ = ⊥
prefix-reflexive {k = ⊥≺xs} ⊥ = ⊥ₗ
prefix-reflexive (x ∷ p) = x ∷ λ where .force → prefix-reflexive (force p)

prefix-trans : ∀ {k} {xs ys zs : Colist⊥ A}
  → Prefix k xs ys
  → Prefix k ys zs
  → Prefix k xs zs
prefix-trans [] _ = []
prefix-trans ⊥ ⊥ = ⊥
prefix-trans ⊥ₗ _ = ⊥ₗ
prefix-trans (x ∷ p) (.x ∷ q) = x ∷ λ where .force → prefix-trans (force p) (force q)

prefix-isPreorder : ∀ {A k} → IsPreorder {A = Colist⊥ A} _≈_ (Prefix k)
prefix-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive = prefix-reflexive
  ; trans = prefix-trans
  }

prefix-preorder : ∀ {A k} → Preorder _ _ _
prefix-preorder {A} {k} = record { isPreorder = prefix-isPreorder {A} {k} }

module PrefixReasoning {A k} where
  open import Relation.Binary.Reasoning.Preorder (prefix-preorder {A} {k}) public

prefix-cong-zip : ∀ {k} {xs' xs : Colist⊥ A} {ys' ys : Colist⊥ B}
  → Prefix k xs' xs
  → Prefix k ys' ys
  → Prefix k (zip xs' ys') (zip xs ys)
prefix-cong-zip ⊥ _ = ⊥
prefix-cong-zip ⊥ₗ _ = ⊥ₗ
prefix-cong-zip {xs = []} [] ⊥ = ⊥
prefix-cong-zip {xs = ⊥} [] ⊥ = ⊥
prefix-cong-zip {xs = x ∷ xs} [] ⊥ = ⊥
prefix-cong-zip (_ ∷ _) ⊥ = ⊥
prefix-cong-zip [] ⊥ₗ = ⊥ₗ
prefix-cong-zip (_ ∷ _) ⊥ₗ = ⊥ₗ
prefix-cong-zip [] [] = []
prefix-cong-zip [] (_ ∷ _) = []
prefix-cong-zip (x ∷ p) [] = []
prefix-cong-zip (x ∷ p) (y ∷ q) = (x , y) ∷ λ where .force → prefix-cong-zip (force p) (force q)

prefix-cong-unzipₗ : ∀ {k} {xys' xys : Colist⊥ (A × B)}
  → Prefix k xys' xys
  → Prefix k (unzipₗ xys') (unzipₗ xys)
prefix-cong-unzipₗ [] = []
prefix-cong-unzipₗ ⊥ = ⊥
prefix-cong-unzipₗ ⊥ₗ = ⊥ₗ
prefix-cong-unzipₗ ((x , _) ∷ p) = x ∷ λ where .force → prefix-cong-unzipₗ (force p)

prefix-cong-unzipᵣ : ∀ {k} {xys' xys : Colist⊥ (A × B)}
  → Prefix k xys' xys
  → Prefix k (unzipᵣ xys') (unzipᵣ xys)
prefix-cong-unzipᵣ [] = []
prefix-cong-unzipᵣ ⊥ = ⊥
prefix-cong-unzipᵣ ⊥ₗ = ⊥ₗ
prefix-cong-unzipᵣ ((_ , y) ∷ q) = y ∷ λ where .force → prefix-cong-unzipᵣ (force q)

zip-unzipₗ : ∀ (xs : Colist⊥ A) (ys : Colist⊥ B) → unzipₗ (zip xs ys) ≺≺ xs
zip-unzipₗ [] [] = []
zip-unzipₗ [] ⊥ = ⊥ₗ
zip-unzipₗ [] (x ∷ xs) = []
zip-unzipₗ ⊥ ys = ⊥ₗ
zip-unzipₗ (x ∷ xs) [] = []
zip-unzipₗ (x ∷ xs) ⊥ = ⊥ₗ
zip-unzipₗ (x ∷ xs) (y ∷ ys) = x ∷ λ where .force → zip-unzipₗ (force xs) (force ys)

zip-unzipᵣ : ∀ (xs : Colist⊥ A) (ys : Colist⊥ B) → unzipᵣ (zip xs ys) ≺≺ ys
zip-unzipᵣ [] [] = []
zip-unzipᵣ [] ⊥ = ⊥ₗ
zip-unzipᵣ [] (x ∷ xs) = []
zip-unzipᵣ ⊥ ys = ⊥ₗ
zip-unzipᵣ (x ∷ xs) [] = []
zip-unzipᵣ (x ∷ xs) ⊥ = ⊥ₗ
zip-unzipᵣ (x ∷ xs) (y ∷ ys) = y ∷ λ where .force → zip-unzipᵣ (force xs) (force ys)
