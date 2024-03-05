{-# OPTIONS --guardedness --cubical #-}

module Codata.PartialConat where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Nat.Properties using ( +-zero ) renaming ( max to _⊔_ )
open import Cubical.Data.Empty.Base as Empty using () renaming ( ⊥ to Empty )
open import Cubical.Data.Unit.Base using ( Unit; tt )
open import Cubical.Relation.Nullary.Base using ( ¬_ )
open import Relation.Binary.Bundles using ( Preorder )
open import Relation.Binary.Structures using ( IsPreorder )

--------------------------------------------------------------------------------
-- Partial Conatural

mutual

  data Coℕ⊥ : Type where
    zero : Coℕ⊥
    ⊥ : Coℕ⊥
    suc : (n : ∞Coℕ⊥) → Coℕ⊥

  record ∞Coℕ⊥ : Type where
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
-- Properties

zero≢⊥ : ¬ zero ≡ ⊥
zero≢⊥ p = subst P p tt
  where
    P : ∀ (n : Coℕ⊥) → Type
    P zero = Unit
    P ⊥ = Empty
    P (suc n) = Empty

zero≢suc : ∀ {n} → ¬ zero ≡ suc n
zero≢suc p = subst P p tt
  where
    P : ∀ (n : Coℕ⊥) → Type
    P zero = Unit
    P ⊥ = Empty
    P (suc n) = Empty

⊥≢suc : ∀ {n} → ¬ ⊥ ≡ suc n
⊥≢suc p = subst P p tt
  where
    P : ∀ (n : Coℕ⊥) → Type
    P zero = Empty
    P ⊥ = Unit
    P (suc n) = Empty

suc-injective : {m n : ∞Coℕ⊥} → suc m ≡ suc n → force m ≡ force n
suc-injective = congS λ where
  zero → zero
  ⊥ → ⊥
  (suc n) → force n

n⊓⊥≡⊥ : ∀ n → n ⊓ ⊥ ≡ ⊥
n⊓⊥≡⊥ zero = refl
n⊓⊥≡⊥ ⊥ = refl
n⊓⊥≡⊥ (suc n) = refl

⊓-idem : ∀ n → n ⊓ n ≡ n
⊓-idem zero = refl
⊓-idem ⊥ = refl
⊓-idem (suc n) i = suc λ where .force → ⊓-idem (force n) i

∸ℕ-+-assoc : ∀ m n o → m ∸ℕ n ∸ℕ o ≡ m ∸ℕ (n + o)
∸ℕ-+-assoc m zero o = refl
∸ℕ-+-assoc m (suc n) zero = congS (λ n → m ∸ℕ suc n) (sym (+-zero n))
∸ℕ-+-assoc zero (suc n) (suc o) = refl
∸ℕ-+-assoc ⊥ (suc n) (suc o) = refl
∸ℕ-+-assoc (suc m) (suc n) (suc o) = ∸ℕ-+-assoc (force m) n (suc o)

[m∸ℕn]⊓m≈m∸ℕn : ∀ m n → (m ∸ℕ n) ⊓ m ≡ m ∸ℕ n
[m∸ℕn]⊓m≈m∸ℕn m zero = ⊓-idem m
[m∸ℕn]⊓m≈m∸ℕn zero (suc n) = refl
[m∸ℕn]⊓m≈m∸ℕn ⊥ (suc n) = refl
[m∸ℕn]⊓m≈m∸ℕn (suc m) (suc n) = lem ([m∸ℕn]⊓m≈m∸ℕn (force m) n)
  where
    lem : ∀ {m n} → m ⊓ n ≡ m → m ⊓ suc (delay n) ≡ m
    lem {zero} {zero} p = p
    lem {⊥} {zero} p = p
    lem {zero} {⊥} p = refl
    lem {⊥} {⊥} p = p
    lem {zero} {suc n} p = p
    lem {⊥} {suc n} p = p
    lem {suc m} {zero} p = Empty.rec (zero≢suc p)
    lem {suc n} {⊥} p = Empty.rec (⊥≢suc p)
    lem {suc m} {suc n} p i = suc λ where .force → lem (suc-injective p) i

m⊓[m∸ℕn]≈m∸ℕn : ∀ m n → m ⊓ (m ∸ℕ n) ≡ m ∸ℕ n
m⊓[m∸ℕn]≈m∸ℕn m zero = ⊓-idem m
m⊓[m∸ℕn]≈m∸ℕn zero (suc n) = refl
m⊓[m∸ℕn]≈m∸ℕn ⊥ (suc n) = refl
m⊓[m∸ℕn]≈m∸ℕn (suc m) (suc n) = lem (m⊓[m∸ℕn]≈m∸ℕn (force m) n)
  where
    lem : ∀ {m n} → m ⊓ n ≡ n → suc (delay m) ⊓ n ≡ n
    lem {zero} {zero} p = p
    lem {zero} {⊥} p = p
    lem {zero} {suc n} p = Empty.rec (zero≢suc p)
    lem {⊥} {zero} p = refl
    lem {⊥} {⊥} p = p
    lem {⊥} {suc n} p = Empty.rec (⊥≢suc p)
    lem {suc m} {zero} p = p
    lem {suc m} {⊥} p = p
    lem {suc m} {suc n} p i = suc λ where .force → lem (suc-injective p) i

∸ℕ-distribˡ-⊔-⊓ : ∀ m n o → m ∸ℕ (n ⊔ o) ≡ (m ∸ℕ n) ⊓ (m ∸ℕ o)
∸ℕ-distribˡ-⊔-⊓ m zero zero = sym (⊓-idem m)
∸ℕ-distribˡ-⊔-⊓ m zero (suc o) = sym (m⊓[m∸ℕn]≈m∸ℕn m (suc o))
∸ℕ-distribˡ-⊔-⊓ m (suc n) zero = sym ([m∸ℕn]⊓m≈m∸ℕn m (suc n))
∸ℕ-distribˡ-⊔-⊓ zero (suc n) (suc o) = refl
∸ℕ-distribˡ-⊔-⊓ ⊥ (suc n) (suc o) = refl
∸ℕ-distribˡ-⊔-⊓ (suc m) (suc n) (suc o) = ∸ℕ-distribˡ-⊔-⊓ (force m) n o

--------------------------------------------------------------------------------
-- Less defined

infix 4 _⊑_ _⊑′_ _∞⊑_

mutual

  data _⊑_ : Coℕ⊥ → Coℕ⊥ → Type where
    con : ∀ {m n} → m ⊑′ n → m ⊑ n

  _⊑′_ : Coℕ⊥ → Coℕ⊥ → Type
  zero ⊑′ zero = Unit
  ⊥ ⊑′ _ = Unit
  suc m ⊑′ suc n = m ∞⊑ n
  _ ⊑′ _ = Empty

  record _∞⊑_ (m n : ∞Coℕ⊥) : Type where
    coinductive
    field force : force m ⊑ force n

open _∞⊑_ public

⊑-refl : ∀ {n} → n ⊑ n
⊑-refl {zero} = con tt
⊑-refl {⊥} = con tt
⊑-refl {suc n} = con λ where .force → ⊑-refl

≡-to-⊑ : ∀ {m n} → m ≡ n → m ⊑ n
≡-to-⊑ eq = subst (_ ⊑_) eq ⊑-refl

⊑-trans : ∀ {m n o} → m ⊑ n → n ⊑ o → m ⊑ o
⊑-trans {⊥} {n} {o} p q = con tt
⊑-trans {zero} {zero} {zero} p q = con tt
⊑-trans {suc m} {suc n} {suc o} (con p) (con q) = con λ where .force → ⊑-trans (force p) (force q)
⊑-trans {zero} {suc _} {o} (con ()) q
⊑-trans {suc _} {zero} {o} (con ()) q
⊑-trans {m} {zero} {suc _} p (con ())
⊑-trans {m} {suc _} {zero} p (con ())
⊑-trans {zero} {⊥} {o} (con ()) q
⊑-trans {m} {zero} {⊥} p (con ())
⊑-trans {suc m} {⊥} {o} (con ()) q
⊑-trans {m} {suc n} {⊥} p (con ())

⊑-isPreorder : IsPreorder _≡_ _⊑_
⊑-isPreorder = record
  { isEquivalence = record { refl = refl; sym = sym; trans = _∙_ }
  ; reflexive = ≡-to-⊑
  ; trans = ⊑-trans
  }

⊑-preorder : Preorder _ _ _
⊑-preorder = record { isPreorder = ⊑-isPreorder }

module ⊑-Reasoning where
  open import Relation.Binary.Reasoning.Preorder ⊑-preorder public

⊑-cong-∸ℕ : ∀ {m n} o → m ⊑ n → m ∸ℕ o ⊑ n ∸ℕ o
⊑-cong-∸ℕ zero p = p
⊑-cong-∸ℕ {zero} {zero} (suc o) (con tt) = con tt
⊑-cong-∸ℕ {zero} {⊥} (suc o) (con ())
⊑-cong-∸ℕ {zero} {suc n} (suc o) (con ())
⊑-cong-∸ℕ {⊥} (suc o) (con tt) = con tt
⊑-cong-∸ℕ {suc m} {zero} (suc o) (con ())
⊑-cong-∸ℕ {suc m} {⊥} (suc o) (con ())
⊑-cong-∸ℕ {suc m} {suc n} (suc o) (con p) = ⊑-cong-∸ℕ o (force p)

⊑-cong-⊓ : ∀ {m n o p} → m ⊑ n → o ⊑ p → m ⊓ o ⊑ n ⊓ p
⊑-cong-⊓ {⊥} {n} {o} {p} q r = con tt
⊑-cong-⊓ {m} {n} {⊥} {p} q r = ⊑-trans (≡-to-⊑ (n⊓⊥≡⊥ m)) (con tt)
⊑-cong-⊓ {zero} {⊥} {o} {p} (con ()) r
⊑-cong-⊓ {zero} {suc _} {o} {p} (con ()) r
⊑-cong-⊓ {suc _} {⊥} {o} {p} (con ()) r
⊑-cong-⊓ {suc _} {zero} {o} {p} (con ()) r
⊑-cong-⊓ {m} {n} {zero} {⊥} q (con ())
⊑-cong-⊓ {m} {n} {zero} {suc _} q (con ())
⊑-cong-⊓ {m} {n} {suc _} {zero} q (con ())
⊑-cong-⊓ {m} {n} {suc _} {⊥} q (con ())
⊑-cong-⊓ {zero} {zero} {zero} {zero} q r = con tt
⊑-cong-⊓ {zero} {zero} {suc o} {suc p} q r = con tt
⊑-cong-⊓ {suc m} {suc n} {zero} {zero} q r = con tt
⊑-cong-⊓ {suc m} {suc n} {suc o} {suc p} (con q) (con r) =
  con λ where .force → ⊑-cong-⊓ (force q) (force r)
