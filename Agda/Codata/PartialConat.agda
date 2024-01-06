{-# OPTIONS --guardedness #-}

module Codata.PartialConat where

open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Nat.Properties using ( +-identityʳ; +-suc )
open import Relation.Binary.Bundles using ( Setoid )
open import Relation.Binary.Structures using ( IsEquivalence )

--------------------------------------------------------------------------------
-- Partial Conatural

mutual

  data Coℕ⊥ : Set where
    zero : Coℕ⊥
    ⊥ : Coℕ⊥
    suc : (n : ∞Coℕ⊥) → Coℕ⊥

  record ∞Coℕ⊥ : Set where
    coinductive
    constructor delay
    field force : Coℕ⊥

open ∞Coℕ⊥ public

-- η is safe for ∞Coℕ⊥
{-# ETA ∞Coℕ⊥ #-}

infixl 6 _∸ℕ_
_∸ℕ_ : Coℕ⊥ → ℕ → Coℕ⊥
m ∸ℕ zero = m
zero ∸ℕ suc n = zero
⊥ ∸ℕ suc n = ⊥
suc m ∸ℕ suc n = force m ∸ℕ n

infixl 7 _⊓_
_⊓_ : Coℕ⊥ → Coℕ⊥ → Coℕ⊥
⊥ ⊓ _ = ⊥
_ ⊓ ⊥ = ⊥
zero ⊓ _ = zero
_ ⊓ zero = zero
suc m ⊓ suc n = suc λ where .force → force m ⊓ force n

--------------------------------------------------------------------------------
-- Bisimulation

infix 4 _≈_ _∞≈_

mutual

  data _≈_ : Coℕ⊥ → Coℕ⊥ → Set where
    zero : zero ≈ zero
    ⊥ : ⊥ ≈ ⊥
    suc : ∀ {m n} (p : m ∞≈ n) → suc m ≈ suc n

  record _∞≈_ (m n : ∞Coℕ⊥) : Set where
    coinductive
    field force : force m ≈ force n

open _∞≈_ public

≈-refl : ∀ {n} → n ≈ n
≈-refl {zero} = zero
≈-refl {⊥} = ⊥
≈-refl {suc n} = suc λ where .force → ≈-refl

≈-sym : ∀ {m n} → m ≈ n → n ≈ m
≈-sym zero = zero
≈-sym ⊥ = ⊥
≈-sym (suc m≈n) = suc λ where .force → ≈-sym (force m≈n)

≈-trans : ∀ {m n o} → m ≈ n → n ≈ o → m ≈ o
≈-trans zero n≈o = n≈o
≈-trans ⊥ n≈o = n≈o
≈-trans (suc m≈n) (suc n≈o) = suc λ where .force → ≈-trans (force m≈n) (force n≈o)

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = ≈-trans
  }

≈-setoid : Setoid _ _
≈-setoid = record { isEquivalence = ≈-isEquivalence }

suc-injective : ∀ {m n} → suc m ≈ suc n → m ∞≈ n
suc-injective (suc p) = p

≈-cong-∸ℕ : ∀ {m n} o → m ≈ n → m ∸ℕ o ≈ n ∸ℕ o
≈-cong-∸ℕ zero m≈n = m≈n
≈-cong-∸ℕ (suc o) zero = zero
≈-cong-∸ℕ (suc o) ⊥ = ⊥
≈-cong-∸ℕ (suc o) (suc m≈n) = ≈-cong-∸ℕ o (force m≈n)

≈-cong-⊓ : ∀ {m n o p} → m ≈ n → o ≈ p → m ⊓ o ≈ n ⊓ p
≈-cong-⊓ zero zero = zero
≈-cong-⊓ zero ⊥ = ⊥
≈-cong-⊓ zero (suc _) = zero
≈-cong-⊓ ⊥ zero = ⊥
≈-cong-⊓ ⊥ ⊥ = ⊥
≈-cong-⊓ ⊥ (suc _) = ⊥
≈-cong-⊓ (suc _) zero = zero
≈-cong-⊓ (suc _) ⊥ = ⊥
≈-cong-⊓ (suc m≈n) (suc o≈p) = suc λ where .force → ≈-cong-⊓ (force m≈n) (force o≈p)

∸ℕ-+-assoc : ∀ m n o → m ∸ℕ n ∸ℕ o ≈ m ∸ℕ (n + o)
∸ℕ-+-assoc m zero o = ≈-refl
∸ℕ-+-assoc m (suc n) zero rewrite +-identityʳ n = ≈-refl
∸ℕ-+-assoc zero (suc n) (suc o) = zero
∸ℕ-+-assoc ⊥ (suc n) (suc o) = ⊥
∸ℕ-+-assoc (suc m) (suc n) (suc o) = ∸ℕ-+-assoc (force m) n (suc o)

⊓-idem : ∀ n → n ⊓ n ≈ n
⊓-idem zero = zero
⊓-idem ⊥ = ⊥
⊓-idem (suc n) = suc λ where .force → ⊓-idem (force n)

[m∸ℕn]⊓m≈m∸ℕn : ∀ m n → (m ∸ℕ n) ⊓ m ≈ m ∸ℕ n
[m∸ℕn]⊓m≈m∸ℕn m zero = ⊓-idem m
[m∸ℕn]⊓m≈m∸ℕn zero (suc n) = zero
[m∸ℕn]⊓m≈m∸ℕn ⊥ (suc n) = ⊥
[m∸ℕn]⊓m≈m∸ℕn (suc m) (suc n) = lem ([m∸ℕn]⊓m≈m∸ℕn (force m) n)
  where
    lem : ∀ {m n} → m ⊓ n ≈ m → m ⊓ suc (delay n) ≈ m
    lem {zero} {zero} p = p
    lem {⊥} {zero} p = p
    lem {zero} {⊥} p = zero
    lem {⊥} {⊥} p = p
    lem {zero} {suc n} p = p
    lem {⊥} {suc n} p = p
    lem {suc m} {suc n} p = suc λ where .force → lem (force (suc-injective p))

m⊓[m∸ℕn]≈m∸ℕn : ∀ m n → m ⊓ (m ∸ℕ n) ≈ m ∸ℕ n
m⊓[m∸ℕn]≈m∸ℕn m zero = ⊓-idem m
m⊓[m∸ℕn]≈m∸ℕn zero (suc n) = zero
m⊓[m∸ℕn]≈m∸ℕn ⊥ (suc n) = ⊥
m⊓[m∸ℕn]≈m∸ℕn (suc m) (suc n) = lem (m⊓[m∸ℕn]≈m∸ℕn (force m) n)
  where
    lem : ∀ {m n} → m ⊓ n ≈ n → suc (delay m) ⊓ n ≈ n
    lem {zero} {zero} p = p
    lem {zero} {⊥} p = p
    lem {⊥} {⊥} p = p
    lem {suc m} {zero} p = p
    lem {suc m} {⊥} p = p
    lem {suc m} {suc n} p = suc λ where .force → lem (force (suc-injective p))

∸ℕ-distribˡ-⊔-⊓ : ∀ m n o → m ∸ℕ (n ⊔ o) ≈ (m ∸ℕ n) ⊓ (m ∸ℕ o)
∸ℕ-distribˡ-⊔-⊓ m zero zero = ≈-sym (⊓-idem m)
∸ℕ-distribˡ-⊔-⊓ m zero (suc o) = ≈-sym (m⊓[m∸ℕn]≈m∸ℕn m (suc o))
∸ℕ-distribˡ-⊔-⊓ m (suc n) zero = ≈-sym ([m∸ℕn]⊓m≈m∸ℕn m (suc n))
∸ℕ-distribˡ-⊔-⊓ zero (suc n) (suc o) = zero
∸ℕ-distribˡ-⊔-⊓ ⊥ (suc n) (suc o) = ⊥
∸ℕ-distribˡ-⊔-⊓ (suc m) (suc n) (suc o) = ∸ℕ-distribˡ-⊔-⊓ (force m) n o

--------------------------------------------------------------------------------
-- More defined

infix 4 _⊑_ _∞⊑_

mutual

  data _⊑_ : Coℕ⊥ → Coℕ⊥ → Set where
    zero : zero ⊑ zero
    ⊥ₗ : ∀ {n} → ⊥ ⊑ n
    suc : ∀ {m n} (p : m ∞⊑ n) → suc m ⊑ suc n

  record _∞⊑_ (m n : ∞Coℕ⊥) : Set where
    coinductive
    field force : force m ⊑ force n

open _∞⊑_ public

⊑-refl : ∀ {n} → n ⊑ n
⊑-refl {zero} = zero
⊑-refl {⊥} = ⊥ₗ
⊑-refl {suc n} = suc λ where .force → ⊑-refl

⊑-trans : ∀ {m n o} → m ⊑ n → n ⊑ o → m ⊑ o
⊑-trans zero q = q
⊑-trans ⊥ₗ q = ⊥ₗ
⊑-trans (suc p) (suc q) = suc λ where .force → ⊑-trans (force p) (force q)

≈-to-⊑ : ∀ {m n} → m ≈ n → m ⊑ n
≈-to-⊑ zero = zero
≈-to-⊑ ⊥ = ⊥ₗ
≈-to-⊑ (suc p) = suc λ where .force → ≈-to-⊑ (force p)

⊑-cong-∸ℕ : ∀ {m n} o → m ⊑ n → m ∸ℕ o ⊑ n ∸ℕ o
⊑-cong-∸ℕ zero p = p
⊑-cong-∸ℕ (suc o) zero = zero
⊑-cong-∸ℕ (suc o) ⊥ₗ = ⊥ₗ
⊑-cong-∸ℕ (suc o) (suc p) = ⊑-cong-∸ℕ o (force p)

⊑-cong-⊓ : ∀ {m n o p} → m ⊑ n → o ⊑ p → m ⊓ o ⊑ n ⊓ p
⊑-cong-⊓ zero zero = zero
⊑-cong-⊓ zero ⊥ₗ = ⊥ₗ
⊑-cong-⊓ zero (suc _) = zero
⊑-cong-⊓ ⊥ₗ zero = ⊥ₗ
⊑-cong-⊓ ⊥ₗ ⊥ₗ = ⊥ₗ
⊑-cong-⊓ ⊥ₗ (suc _) = ⊥ₗ
⊑-cong-⊓ (suc _) zero = zero
⊑-cong-⊓ (suc _) ⊥ₗ = ⊥ₗ
⊑-cong-⊓ (suc p) (suc q) = suc λ where .force → ⊑-cong-⊓ (force p) (force q)
