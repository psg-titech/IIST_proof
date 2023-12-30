{-# OPTIONS --guardedness #-}

module IIST.Experiment.PartialColist where

open import IIST.Experiment.PartialConat as Coℕˣ using ( Coℕˣ; zero; suc; fail; force )

private
  variable
    A B : Set

--------------------------------------------------------------------------------
-- Partial colist

mutual

  data Colistˣ (A : Set) : Set where
    [] : Colistˣ A
    _∷_ : A → ∞Colistˣ A → Colistˣ A
    fail : ∞Colistˣ A → Colistˣ A

  record ∞Colistˣ (A : Set) : Set where
    coinductive
    field force : Colistˣ A

open ∞Colistˣ public

{-# ETA ∞Colistˣ #-}

colength : Colistˣ A → Coℕˣ
colength [] = zero
colength (x ∷ xs) = suc λ where .force → colength (force xs)
colength (fail xs) = fail λ where .force → colength (force xs)

--------------------------------------------------------------------------------
-- More defined

mutual

  data _⊑_ {A} : Colistˣ A → Colistˣ A → Set where
    [] : [] ⊑ []
    _∷_ : ∀ x {xs ys} (p : xs ∞⊑ ys) → (x ∷ xs) ⊑ (x ∷ ys)
    fail : ∀ {xs ys} (p : xs ∞⊑ ys) → fail xs ⊑ fail ys
    failₗ : ∀ {xs ys} (p : force xs ⊑ ys) → fail xs ⊑ ys

  record _∞⊑_ (xs ys : ∞Colistˣ A) : Set where
    coinductive
    field force : force xs ⊑ force ys

open _∞⊑_ public

⊑-refl : ∀ {xs : Colistˣ A} → xs ⊑ xs
⊑-refl {xs = []} = []
⊑-refl {xs = x ∷ xs} = x ∷ λ where .force → ⊑-refl
⊑-refl {xs = fail xs} = fail λ where .force → ⊑-refl

⊑-trans : ∀ {xs ys zs : Colistˣ A} → xs ⊑ ys → ys ⊑ zs → xs ⊑ zs
⊑-trans [] [] = []
⊑-trans (x ∷ p) (.x ∷ q) = x ∷ λ where .force → ⊑-trans (force p) (force q)
⊑-trans (fail p) (fail q) = fail λ where .force → ⊑-trans (force p) (force q)
⊑-trans (fail p) (failₗ q) = failₗ (⊑-trans (force p) q)
⊑-trans (failₗ p) q = failₗ (⊑-trans p q)

--------------------------------------------------------------------------------
-- More defined + Prefix

mutual

  data _≺_ {A} : Colistˣ A → Colistˣ A → Set where
    [] : ∀ {xs} → [] ≺ xs
    _∷_ : ∀ x {xs ys} (p : xs ∞≺ ys) → (x ∷ xs) ≺ (x ∷ ys)
    fail : ∀ {xs ys} (p : xs ∞≺ ys) → fail xs ≺ fail ys
    failₗ : ∀ {xs ys} (p : force xs ≺ ys) → fail xs ≺ ys

  record _∞≺_ (xs ys : ∞Colistˣ A) : Set where
    coinductive
    field force : force xs ≺ force ys

open _∞≺_ public

≺-refl : ∀ {xs : Colistˣ A} → xs ≺ xs
≺-refl {xs = []} = []
≺-refl {xs = x ∷ xs} = x ∷ λ where .force → ≺-refl
≺-refl {xs = fail xs} = fail λ where .force → ≺-refl

≺-trans : ∀ {xs ys zs : Colistˣ A} → xs ≺ ys → ys ≺ zs → xs ≺ zs
≺-trans [] _ = []
≺-trans (x ∷ p) (.x ∷ q) = x ∷ λ where .force → ≺-trans (force p) (force q)
≺-trans (fail p) (fail q) = fail λ where .force → ≺-trans (force p) (force q)
≺-trans (fail p) (failₗ q) = failₗ (≺-trans (force p) q)
≺-trans (failₗ p) q = failₗ (≺-trans p q)
