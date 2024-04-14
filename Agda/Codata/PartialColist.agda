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
    A B C : Set

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
-- Evantually ⊥

data Eventually⊥ {A} : Colist⊥ A → Set where
  ⊥ : Eventually⊥ ⊥
  _∷_ : ∀ x {xs} → Eventually⊥ (force xs) → Eventually⊥ (x ∷ xs)

--------------------------------------------------------------------------------
-- No⊥

mutual

  data No⊥ {A} : Colist⊥ A → Set where
    [] : No⊥ []
    _∷_ : ∀ x {xs} → ∞No⊥ xs → No⊥ (x ∷ xs)

  record ∞No⊥ (xs : ∞Colist⊥ A) : Set where
    coinductive
    constructor delay
    field force : No⊥ (force xs)

open ∞No⊥ public

map-pres-no⊥ : ∀ (f : A → B) {xs}
  → No⊥ xs
  → No⊥ (map f xs)
map-pres-no⊥ f [] = []
map-pres-no⊥ f (x ∷ xs) =
  f x ∷ λ where .force → map-pres-no⊥ f (force xs)

zip-pres-no⊥ : {xs : Colist⊥ A} {ys : Colist⊥ B}
  → No⊥ xs
  → No⊥ ys
  → No⊥ (zip xs ys)
zip-pres-no⊥ [] [] = []
zip-pres-no⊥ [] (y ∷ ys) = []
zip-pres-no⊥ (x ∷ xs) [] = []
zip-pres-no⊥ (x ∷ xs) (y ∷ ys) =
  (x , y) ∷ λ where .force → zip-pres-no⊥ (force xs) (force ys)

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
{-# DISPLAY Prefix ⊥≺⊥ xs ys = xs ≺ ys #-}
{-# DISPLAY Prefix ⊥≺xs xs ys = xs ≺≺ ys #-}

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
prefix-cong-zip (x ∷ p) (y ∷ q) =
  (x , y) ∷ λ where .force → prefix-cong-zip (force p) (force q)

prefix-cong-unzipₗ : ∀ {k} {xys' xys : Colist⊥ (A × B)}
  → Prefix k xys' xys
  → Prefix k (unzipₗ xys') (unzipₗ xys)
prefix-cong-unzipₗ [] = []
prefix-cong-unzipₗ ⊥ = ⊥
prefix-cong-unzipₗ ⊥ₗ = ⊥ₗ
prefix-cong-unzipₗ ((x , _) ∷ p) =
  x ∷ λ where .force → prefix-cong-unzipₗ (force p)

prefix-cong-unzipᵣ : ∀ {k} {xys' xys : Colist⊥ (A × B)}
  → Prefix k xys' xys
  → Prefix k (unzipᵣ xys') (unzipᵣ xys)
prefix-cong-unzipᵣ [] = []
prefix-cong-unzipᵣ ⊥ = ⊥
prefix-cong-unzipᵣ ⊥ₗ = ⊥ₗ
prefix-cong-unzipᵣ ((_ , y) ∷ q) =
  y ∷ λ where .force → prefix-cong-unzipᵣ (force q)

zip-unzipₗ : ∀ (xs : Colist⊥ A) (ys : Colist⊥ B) → unzipₗ (zip xs ys) ≺≺ xs
zip-unzipₗ [] [] = []
zip-unzipₗ [] ⊥ = ⊥ₗ
zip-unzipₗ [] (x ∷ xs) = []
zip-unzipₗ ⊥ ys = ⊥ₗ
zip-unzipₗ (x ∷ xs) [] = []
zip-unzipₗ (x ∷ xs) ⊥ = ⊥ₗ
zip-unzipₗ (x ∷ xs) (y ∷ ys) =
  x ∷ λ where .force → zip-unzipₗ (force xs) (force ys)

zip-unzipᵣ : ∀ (xs : Colist⊥ A) (ys : Colist⊥ B) → unzipᵣ (zip xs ys) ≺≺ ys
zip-unzipᵣ [] [] = []
zip-unzipᵣ [] ⊥ = ⊥ₗ
zip-unzipᵣ [] (x ∷ xs) = []
zip-unzipᵣ ⊥ ys = ⊥ₗ
zip-unzipᵣ (x ∷ xs) [] = []
zip-unzipᵣ (x ∷ xs) ⊥ = ⊥ₗ
zip-unzipᵣ (x ∷ xs) (y ∷ ys) =
  y ∷ λ where .force → zip-unzipᵣ (force xs) (force ys)

≺-to-≺≺ : ∀ {xs ys : Colist⊥ A} → xs ≺ ys → xs ≺≺ ys
≺-to-≺≺ [] = []
≺-to-≺≺ ⊥ = ⊥ₗ
≺-to-≺≺ (x ∷ p) = x ∷ λ where .force → ≺-to-≺≺ (force p)

≺≺-to-≺ : ∀ {xs ys : Colist⊥ A}
  → xs ≺≺ ys
  → No⊥ xs
  → xs ≺ ys
≺≺-to-≺ [] [] = []
≺≺-to-≺ (x ∷ p) (.x ∷ q) =
  x ∷ λ where .force → ≺≺-to-≺ (force p) (force q)

≺-no⊥ : ∀ {xs ys : Colist⊥ A}
  → xs ≺ ys
  → No⊥ ys
  → No⊥ xs
≺-no⊥ [] [] = []
≺-no⊥ [] (x ∷ q) = []
≺-no⊥ (x ∷ p) (.x ∷ q) =
  x ∷ λ where .force → ≺-no⊥ (force p) (force q)

--------------------------------------------------------------------------------

infix 4 _≺₂_ _∞≺₂_

mutual

  data _≺₂_ {A} : Colist⊥ A → Colist⊥ A → Set where
    [] : [] ≺₂ []
    []ₗ : ∀ {y ys} → delay [] ∞≺₂ ys → [] ≺₂ y ∷ ys
    ⊥ₗ : ∀ {ys} → ⊥ ≺₂ ys
    _∷_ : ∀ x {xs ys} → xs ∞≺₂ ys → x ∷ xs ≺₂ x ∷ ys

  record _∞≺₂_ (xs ys : ∞Colist⊥ A) : Set where
    coinductive
    field force : force xs ≺₂ force ys

open _∞≺₂_ public

≺₂-reflexive : ∀ {xs ys : Colist⊥ A} → xs ≈ ys → xs ≺₂ ys
≺₂-reflexive [] = []
≺₂-reflexive ⊥ = ⊥ₗ
≺₂-reflexive (x ∷ p) = x ∷ λ where .force → ≺₂-reflexive (force p)

≺₂-trans : ∀ {xs ys zs : Colist⊥ A} → xs ≺₂ ys → ys ≺₂ zs → xs ≺₂ zs
≺₂-trans [] [] = []
≺₂-trans [] ([]ₗ q) = []ₗ λ where .force → ≺₂-trans [] (force q)
≺₂-trans ([]ₗ p) (_ ∷ q) = []ₗ λ where .force → ≺₂-trans (force p) (force q)
≺₂-trans ⊥ₗ q = ⊥ₗ
≺₂-trans (x ∷ p) (.x ∷ q) = x ∷ λ where .force → ≺₂-trans (force p) (force q)

≺₂-isPreorder : ∀ {A} → IsPreorder {A = Colist⊥ A} _≈_ _≺₂_
≺₂-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive = ≺₂-reflexive
  ; trans = ≺₂-trans
  }

≺₂-preorder : ∀ {A} → Preorder _ _ _
≺₂-preorder {A} = record { isPreorder = ≺₂-isPreorder {A} }

module ≺₂-Reasoning {A} where
  open import Relation.Binary.Reasoning.Preorder (≺₂-preorder {A}) public

--------------------------------------------------------------------------------

infix 4 _⊑_ _∞⊑_
infix 5 -∷_

mutual

  -- _⊑_ is a (heterogeneous) preorder that expresses:
  --   * ⊥ should appear in LHS if it appears in RHS and
  --   * ⊥ should not appear in RHS if it does not appear in LHS
  -- So, from xs ⊑ ys it follows that (No⊥ xs → No⊥ ys) and (Eventually⊥ ys → Eventually⊥ xs)
  data _⊑_ {A B} : Colist⊥ A → Colist⊥ B → Set where
    []ₗ : ∀ {y ys} → delay ([] {A}) ∞⊑ ys → [] ⊑ y ∷ ys
    []ᵣ : ∀ {xs} → xs ⊑ []
    ⊥ₗ : ∀ {ys} → ⊥ ⊑ ys
    ⊥ᵣ : ∀ {x xs} → force xs ⊑ ⊥ {B} → x ∷ xs ⊑ ⊥
    -- Note:                 ^ here _⊑_ is used, not _∞⊑_
    -∷_ : ∀ {x y xs ys} → xs ∞⊑ ys → x ∷ xs ⊑ y ∷ ys

  record _∞⊑_ (xs : ∞Colist⊥ A) (ys : ∞Colist⊥ B) : Set where
    coinductive
    field force : force xs ⊑ force ys

open _∞⊑_ public

⊑-reflexive : {xs ys : Colist⊥ A}
  → xs ≈ ys
  → xs ⊑ ys
⊑-reflexive [] = []ᵣ
⊑-reflexive ⊥ = ⊥ₗ
⊑-reflexive (x ∷ p) = -∷ λ where .force → ⊑-reflexive (force p)

⊑-trans : {xs : Colist⊥ A} {ys : Colist⊥ B} {zs : Colist⊥ C}
  → xs ⊑ ys
  → ys ⊑ zs
  → xs ⊑ zs
⊑-trans p []ᵣ = []ᵣ
⊑-trans ⊥ₗ q = ⊥ₗ
⊑-trans ([]ₗ p) (⊥ᵣ q) = ⊑-trans (force p) q
⊑-trans ([]ₗ p) (-∷ q) = []ₗ λ where .force → ⊑-trans (force p) (force q)
⊑-trans {xs = []} []ᵣ ([]ₗ q) = []ₗ λ where .force → ⊑-trans []ᵣ (force q)
⊑-trans {xs = ⊥} []ᵣ ([]ₗ q) = ⊥ₗ
⊑-trans {xs = x ∷ xs} []ᵣ ([]ₗ q) = -∷ λ where .force → ⊑-trans []ᵣ (force q)
⊑-trans {zs = []} (⊥ᵣ p) ⊥ₗ = []ᵣ
⊑-trans {zs = ⊥} (⊥ᵣ p) ⊥ₗ = ⊥ᵣ (⊑-trans p ⊥ₗ)
⊑-trans {zs = z ∷ zs} (⊥ᵣ p) ⊥ₗ = -∷ λ where .force → ⊑-trans p ⊥ₗ
⊑-trans (-∷ p) (⊥ᵣ q) = ⊥ᵣ (⊑-trans (force p) q)
⊑-trans (-∷ p) (-∷ q) = -∷ λ where .force → ⊑-trans (force p) (force q)

⊑-isPreorder : ∀ {A} → IsPreorder {A = Colist⊥ A} _≈_ _⊑_
⊑-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive = ⊑-reflexive
  ; trans = ⊑-trans
  }

⊑-preorder : ∀ {A} → Preorder _ _ _
⊑-preorder {A} = record { isPreorder = ⊑-isPreorder {A} }

module ⊑-Reasoning {A} where
  open import Relation.Binary.Reasoning.Preorder (⊑-preorder {A}) public

⊑-cons : ∀ (x : A) xs → xs ⊑ x ∷ delay xs
⊑-cons x [] = []ₗ λ where .force → []ᵣ
⊑-cons x ⊥ = ⊥ₗ
⊑-cons x (y ∷ xs) = -∷ λ where .force → ⊑-cons y (force xs)

⊑-uncons : ∀ (x : A) xs → x ∷ delay xs ⊑ xs
⊑-uncons x [] = []ᵣ
⊑-uncons x ⊥ = ⊥ᵣ ⊥ₗ
⊑-uncons x (y ∷ xs) = -∷ λ where .force → ⊑-uncons y (force xs)

⊑-map : ∀ (f : A → B) xs → xs ⊑ map f xs
⊑-map f [] = []ᵣ
⊑-map f ⊥ = ⊥ₗ
⊑-map f (x ∷ xs) = -∷ λ where .force → ⊑-map f (force xs)

⊑-map⁻ : ∀ (f : A → B) xs → map f xs ⊑ xs
⊑-map⁻ f [] = []ᵣ
⊑-map⁻ f ⊥ = ⊥ₗ
⊑-map⁻ f (x ∷ xs) = -∷ λ where .force → ⊑-map⁻ f (force xs)

≺-to-⊑ : ∀ {xs ys : Colist⊥ A}
  → xs ≺ ys
  → ys ⊑ xs
≺-to-⊑ [] = []ᵣ
≺-to-⊑ ⊥ = ⊥ₗ
≺-to-⊑ (x ∷ p) = -∷ λ where .force → ≺-to-⊑ (force p)

≺₂-to-⊑ : ∀ {xs ys : Colist⊥ A} → xs ≺₂ ys → xs ⊑ ys
≺₂-to-⊑ [] = []ᵣ
≺₂-to-⊑ ([]ₗ p) = []ₗ λ where .force → ≺₂-to-⊑ (force p)
≺₂-to-⊑ ⊥ₗ = ⊥ₗ
≺₂-to-⊑ (x ∷ p) = -∷ λ where .force → ≺₂-to-⊑ (force p)

-- interaction with No⊥ and Eventually⊥

⊑-no⊥ : ∀ {xs : Colist⊥ A} {ys : Colist⊥ B}
  → xs ⊑ ys
  → (No⊥ xs → No⊥ ys)
⊑-no⊥ ([]ₗ p) [] = _ ∷ λ where .force → ⊑-no⊥ (force p) []
⊑-no⊥ []ᵣ q = []
⊑-no⊥ (⊥ᵣ p) (_ ∷ q) = ⊑-no⊥ p (force q)
⊑-no⊥ (-∷ p) (_ ∷ q) = _ ∷ λ where .force → ⊑-no⊥ (force p) (force q)

⊑-eventually⊥ : ∀ {xs : Colist⊥ A} {ys : Colist⊥ B}
  → xs ⊑ ys
  → (Eventually⊥ ys → Eventually⊥ xs)
⊑-eventually⊥ ([]ₗ p) (_ ∷ q) = ⊑-eventually⊥ (force p) q
⊑-eventually⊥ ⊥ₗ q = ⊥
⊑-eventually⊥ (⊥ᵣ p) ⊥ = _ ∷ ⊑-eventually⊥ p ⊥
⊑-eventually⊥ (-∷ p) (_ ∷ q) = _ ∷ ⊑-eventually⊥ (force p) q

⊑-no⊥′ : ∀ (xs : Colist⊥ A) {ys : Colist⊥ B}
  → No⊥ ys
  → xs ⊑ ys
⊑-no⊥′ xs [] = []ᵣ
⊑-no⊥′ [] (y ∷ p) = []ₗ λ where .force → ⊑-no⊥′ _ (force p)
⊑-no⊥′ ⊥ (y ∷ p) = ⊥ₗ
⊑-no⊥′ (x ∷ xs) (y ∷ p) = -∷ λ where .force → ⊑-no⊥′ (force xs) (force p)

⊑-eventually⊥′ : ∀ {xs : Colist⊥ A} (ys : Colist⊥ B)
  → Eventually⊥ xs
  → xs ⊑ ys
⊑-eventually⊥′ ys ⊥ = ⊥ₗ
⊑-eventually⊥′ [] (x ∷ p) = []ᵣ
⊑-eventually⊥′ ⊥ (x ∷ p) = ⊥ᵣ (⊑-eventually⊥′ ⊥ p)
⊑-eventually⊥′ (y ∷ ys) (x ∷ p) = -∷ λ where .force → ⊑-eventually⊥′ (force ys) p
