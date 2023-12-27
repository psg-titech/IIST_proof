{-# OPTIONS --guardedness #-}

module Codata.FallibleConat where

open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Nat.Properties using ( +-identityʳ; +-suc )

--------------------------------------------------------------------------------
-- Fallible Conatural

mutual

  data Coℕˣ : Set where
    zero : Coℕˣ
    fail : Coℕˣ
    suc : ∞Coℕˣ → Coℕˣ

  record ∞Coℕˣ : Set where
    coinductive
    constructor delay
    field force : Coℕˣ

open ∞Coℕˣ public

-- η is safe for ∞Coℕˣ
{-# ETA ∞Coℕˣ #-}

_∸ℕ_ : Coℕˣ → ℕ → Coℕˣ
m ∸ℕ zero = m
zero ∸ℕ suc n = zero
fail ∸ℕ suc n = fail
suc m ∸ℕ suc n = force m ∸ℕ n

_⊓_ : Coℕˣ → Coℕˣ → Coℕˣ
zero ⊓ n = zero
fail ⊓ n = fail
suc m ⊓ zero = zero
suc m ⊓ fail = fail
suc m ⊓ suc n = suc λ where .force → force m ⊓ force n

--------------------------------------------------------------------------------
-- Bisimulation

mutual

  data _≈_ : Coℕˣ → Coℕˣ → Set where
    zero : zero ≈ zero
    fail : fail ≈ fail
    suc : ∀ {m n} → m ∞≈ n → suc m ≈ suc n

  record _∞≈_ (m n : ∞Coℕˣ) : Set where
    coinductive
    field force : force m ≈ force n

open _∞≈_ public

≈-refl : ∀ {n} → n ≈ n
≈-refl {zero} = zero
≈-refl {fail} = fail
≈-refl {suc n} = suc λ where .force → ≈-refl

≈-sym : ∀ {m n} → m ≈ n → n ≈ m
≈-sym zero = zero
≈-sym fail = fail
≈-sym (suc m≈n) = suc λ where .force → ≈-sym (force m≈n)

≈-trans : ∀ {m n o} → m ≈ n → n ≈ o → m ≈ o
≈-trans zero n≈o = n≈o
≈-trans fail n≈o = n≈o
≈-trans (suc m≈n) (suc n≈o) = suc λ where .force → ≈-trans (force m≈n) (force n≈o)

≈-∸ℕ : ∀ {m n} o → m ≈ n → (m ∸ℕ o) ≈ (n ∸ℕ o)
≈-∸ℕ zero m≈n = m≈n
≈-∸ℕ (suc o) zero = zero
≈-∸ℕ (suc o) fail = fail
≈-∸ℕ (suc o) (suc m≈n) = ≈-∸ℕ o (force m≈n)

∸-+-assoc : ∀ m n o → ((m ∸ℕ n) ∸ℕ o) ≈ (m ∸ℕ (n + o))
∸-+-assoc m zero o = ≈-refl
∸-+-assoc m (suc n) zero rewrite +-identityʳ n = ≈-refl
∸-+-assoc zero (suc n) (suc o) = zero
∸-+-assoc fail (suc n) (suc o) = fail
∸-+-assoc (suc m) (suc n) (suc o) = ∸-+-assoc (force m) n (suc o)

⊓-idem : ∀ n → (n ⊓ n) ≈ n
⊓-idem zero = zero
⊓-idem fail = fail
⊓-idem (suc n) = suc λ where .force → ⊓-idem (force n)

-- What is (∞ ⊓ ∞) ?
-- ⊓-∸ₗ : ∀ m n → ((m ∸ℕ n) ⊓ m) ≈ (m ∸ℕ n)
-- ⊓-∸ₗ m zero = ⊓-idem m
-- ⊓-∸ₗ zero (suc n) = zero
-- ⊓-∸ₗ fail (suc n) = fail
-- ⊓-∸ₗ (suc m) (suc n) = {!   !}

-- ⊓-∸ᵣ : ∀ m n → (m ⊓ (m ∸ℕ n)) ≈ (m ∸ℕ n)
-- ⊓-∸ᵣ m zero = ⊓-idem m
-- ⊓-∸ᵣ zero (suc n) = zero
-- ⊓-∸ᵣ fail (suc n) = fail
-- ⊓-∸ᵣ (suc m) (suc n) = {!   !}

-- ∸ℕ-distribˡ-⊔-⊓ : ∀ m n o → (m ∸ℕ (n ⊔ o)) ≈ ((m ∸ℕ n) ⊓ (m ∸ℕ o))
-- ∸ℕ-distribˡ-⊔-⊓ m zero zero = ≈-sym (⊓-idem m)
-- ∸ℕ-distribˡ-⊔-⊓ m zero (suc o) = ≈-sym (⊓-∸ᵣ m (suc o))
-- ∸ℕ-distribˡ-⊔-⊓ m (suc n) zero = ≈-sym (⊓-∸ₗ m (suc n))
-- ∸ℕ-distribˡ-⊔-⊓ zero (suc n) (suc o) = zero
-- ∸ℕ-distribˡ-⊔-⊓ fail (suc n) (suc o) = fail
-- ∸ℕ-distribˡ-⊔-⊓ (suc m) (suc n) (suc o) = ∸ℕ-distribˡ-⊔-⊓ (force m) n o
