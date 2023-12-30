{-

Partial conaturals and relations, taken from https://lists.chalmers.se/pipermail/agda/2009/001132.html

-}

{-# OPTIONS --guardedness #-}

module IIST.Experiment.PartialConat where

--------------------------------------------------------------------------------
-- Partial conatural

mutual

  data Coℕˣ : Set where
    zero : Coℕˣ
    suc : (n : ∞Coℕˣ) → Coℕˣ
    fail : (n : ∞Coℕˣ) → Coℕˣ

  record ∞Coℕˣ : Set where
    coinductive
    field force : Coℕˣ

open ∞Coℕˣ

{-# ETA ∞Coℕˣ #-}

--------------------------------------------------------------------------------
-- More defined

mutual

  data _⊑_ : Coℕˣ → Coℕˣ → Set where
    zero : zero ⊑ zero
    suc : ∀ {m n} (p : m ∞⊑ n) → suc m ⊑ suc n
    fail : ∀ {m n} (p : m ∞⊑ n) → fail m ⊑ fail n
    failₗ : ∀ {m n} (p : force m ⊑ n) → fail m ⊑ n

  record _∞⊑_ (m n : ∞Coℕˣ) : Set where
    coinductive
    field force : force m ⊑ force n

open _∞⊑_

⊑-refl : ∀ {n} → n ⊑ n
⊑-refl {zero} = zero
⊑-refl {suc n} = suc λ where .force → ⊑-refl
⊑-refl {fail n} = fail λ where .force → ⊑-refl

⊑-trans : ∀ {m n o} → m ⊑ n → n ⊑ o → m ⊑ o
⊑-trans zero zero = zero
⊑-trans (suc p) (suc q) = suc λ where .force → ⊑-trans (force p) (force q)
⊑-trans (fail p) (fail q) = fail λ where .force → ⊑-trans (force p) (force q)
⊑-trans (fail p) (failₗ q) = failₗ (⊑-trans (force p) q)
⊑-trans (failₗ p) q = failₗ (⊑-trans p q)

--------------------------------------------------------------------------------
-- Bisimulation?

mutual

  data _≈_ : Coℕˣ → Coℕˣ → Set where
    zero : zero ≈ zero
    suc : ∀ {m n} (p : m ∞≈ n) → suc m ≈ suc n
    fail : ∀ {m n} (p : m ∞≈ n) → fail m ≈ fail n
    failₗ : ∀ {m n} (p : force m ≈ n) → fail m ≈ n
    failᵣ : ∀ {m n} (p : m ≈ force n) → m ≈ fail n

  record _∞≈_ (m n : ∞Coℕˣ) : Set where
    coinductive
    field force : force m ≈ force n

open _∞≈_

failₗ⁻¹ : ∀ {m n} → fail m ≈ n → force m ≈ n
failₗ⁻¹ (fail p) = failᵣ (force p)
failₗ⁻¹ (failₗ p) = p
failₗ⁻¹ (failᵣ p) = failᵣ (failₗ⁻¹ p)

failᵣ⁻¹ : ∀ {m n} → m ≈ fail n → m ≈ force n
failᵣ⁻¹ (fail p) = failₗ (force p)
failᵣ⁻¹ (failₗ p) = failₗ (failᵣ⁻¹ p)
failᵣ⁻¹ (failᵣ p) = p

≈-refl : ∀ {n} → n ≈ n
≈-refl {zero} = zero
≈-refl {suc n} = suc λ where .force → ≈-refl
≈-refl {fail n} = fail λ where .force → ≈-refl

≈-sym : ∀ {m n} → m ≈ n → n ≈ m
≈-sym zero = zero
≈-sym (suc p) = suc λ where .force → ≈-sym (force p)
≈-sym (fail p) = fail λ where .force → ≈-sym (force p)
≈-sym (failₗ p) = failᵣ (≈-sym p)
≈-sym (failᵣ p) = failₗ (≈-sym p)

≈-trans : ∀ {m n o} → m ≈ n → n ≈ o → m ≈ o
≈-trans {zero} p q = tr p q
  where
    tr : ∀ {m n} → zero ≈ m → m ≈ n → zero ≈ n
    tr zero q = q
    tr (failᵣ p) q = tr p (failₗ⁻¹ q)
≈-trans {suc n} p q = tr p q
  where
    tr : ∀ {m n o} → suc m ≈ n → n ≈ o → suc m ≈ o
    tr (suc p) (suc q) = suc λ where .force → ≈-trans (force p) (force q)
    tr p (failᵣ q) = failᵣ (tr p q)
    tr (failᵣ p) q = tr p (failₗ⁻¹ q)
≈-trans {fail n} p q = tr p q
  where
    tr : ∀ {m n o} → fail m ≈ n → n ≈ o → fail m ≈ o
    tr p (fail q) = fail λ where .force → ≈-trans (failₗ⁻¹ p) (failₗ (force q))
    tr p (failₗ q) = tr (failᵣ⁻¹ p) q
    tr p (failᵣ q) = fail λ where .force → ≈-trans (failₗ⁻¹ p) q
    tr (failₗ p) q = failₗ (≈-trans p q)
