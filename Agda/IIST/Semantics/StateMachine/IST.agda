{-# OPTIONS --guardedness #-}

module IIST.Semantics.StateMachine.IST where

open import Codata.Musical.Notation
open import Codata.Musical.Colist.Base using ( Colist; []; _∷_ )
open import Codata.Musical.Colist.Bisimilarity using ( []; _∷_ ) renaming ( _≈_ to Bisim )
open import Codata.Musical.Stream using ( Stream; _∷_ )
open import Data.Maybe.Base as Maybe using ( Maybe; just; nothing )
open import Data.Nat.Base using ( ℕ; zero; suc; pred; _+_ )
open import Data.Nat.Properties using ( +-suc; +-assoc; +-identityʳ; suc-injective )
open import Data.Nat.Instances
open import Data.List.Base using ( List; []; _∷_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using ( recompute )

open import IIST.Common
open import IIST.Syntax

private
  variable
    A X Y Z U V W : Set
    d d₁ d₂ d₃ d₄ : ℕ

--------------------------------------------------------------------------------
-- Definitionally d-incremental sequence transformation

record IST (X Y : Set) (d : ℕ) : Set
data Step (X Y : Set) : ℕ → Set

record IST X Y d where
  coinductive
  field step : X → Step X Y d

data Step X Y where
  ⊥ : Step X Y d
  next : IST X Y d → Step X Y (suc d)
  yield : Y → IST X Y 0 → Step X Y 0

open IST public

eat : IST X Y d → List X → Maybe (List Y)
eatₛ : Step X Y d → List X → Maybe (List Y)
eat f [] = just []
eat f (x ∷ xs) = eatₛ (step f x) xs
eatₛ ⊥ xs = nothing
eatₛ (next f) xs = eat f xs
eatₛ (yield y f) xs = Maybe.map (y ∷_) (eat f xs)

eat∞ : IST X Y d → Stream X → Colist Y
eatₛ∞ : Step X Y d → ∞ (Stream X) → Colist Y
eat∞ f (x ∷ xs) = eatₛ∞ (step f x) xs
eatₛ∞ ⊥ xs = []
eatₛ∞ (next f) xs = eat∞ f (♭ xs)
eatₛ∞ (yield y f) xs = y ∷ ♯ eat∞ f (♭ xs)

cast : .(d₁ ≡ d₂) → IST X Y d₁ → IST X Y d₂
castₛ : .(d₁ ≡ d₂) → Step X Y d₁ → Step X Y d₂
step (cast eq f) x = castₛ eq (step f x)
castₛ {d₂ = zero} eq ⊥ = ⊥
castₛ {d₂ = zero} eq (yield y f) = yield y f
castₛ {d₂ = suc d₂} eq ⊥ = ⊥
castₛ {d₂ = suc d₂} eq (next f) = next (cast (cong pred eq) f)

--------------------------------------------------------------------------------
-- Bisimulation

infix 4 _≈_ _≈ₛ_

record _≈_ (f : IST X Y d₁) (g : IST X Y d₂) : Set
data _≈ₛ_ {X Y} : Step X Y d₁ → Step X Y d₂ → Set

record _≈_ {X Y d₁ d₂} f g where
  coinductive
  field
    same-d : d₁ ≡ d₂
    step : ∀ (x : X) → step f x ≈ₛ step g x

data _≈ₛ_ {X Y} where
  ⊥ : ⊥ {d = d₁} ≈ₛ ⊥ {d = d₂}
  next : {f : IST X Y d₁} {g : IST X Y d₂} (p : f ≈ g) → next f ≈ₛ next g
  yield : ∀ x {f g} (p : f ≈ g) → yield x f ≈ₛ yield x g

open _≈_ public

≈-refl : {f : IST X Y d} → f ≈ f
≈ₛ-refl : {s : Step X Y d} → s ≈ₛ s
same-d ≈-refl = refl
step ≈-refl x = ≈ₛ-refl
≈ₛ-refl {s = ⊥} = ⊥
≈ₛ-refl {s = next f} = next ≈-refl
≈ₛ-refl {s = yield x f} = yield x ≈-refl

≈-sym : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → g ≈ f
≈ₛ-sym : {s : Step X Y d₁} {t : Step X Y d₂} → s ≈ₛ t → t ≈ₛ s
same-d (≈-sym f≈g) = sym (same-d f≈g)
step (≈-sym f≈g) x = ≈ₛ-sym (step f≈g x)
≈ₛ-sym ⊥ = ⊥
≈ₛ-sym (next f≈g) = next (≈-sym f≈g)
≈ₛ-sym (yield x f≈g) = yield x (≈-sym f≈g)

≈-trans : {f : IST X Y d₁} {g : IST X Y d₂} {h : IST X Y d₃} → f ≈ g → g ≈ h → f ≈ h
≈ₛ-trans : {s : Step X Y d₁} {t : Step X Y d₂} {u : Step X Y d₃} → s ≈ₛ t → t ≈ₛ u → s ≈ₛ u
same-d (≈-trans f≈g g≈h) = trans (same-d f≈g) (same-d g≈h)
step (≈-trans f≈g g≈h) x = ≈ₛ-trans (step f≈g x) (step g≈h x)
≈ₛ-trans ⊥ ⊥ = ⊥
≈ₛ-trans (next f≈g) (next g≈h) = next (≈-trans f≈g g≈h)
≈ₛ-trans (yield x f≈g) (yield .x g≈h) = yield x (≈-trans f≈g g≈h)

≈-eat : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → ∀ xs → eat f xs ≡ eat g xs
≈ₛ-eatₛ : {s : Step X Y d₁} {t : Step X Y d₂} → s ≈ₛ t → ∀ xs → eatₛ s xs ≡ eatₛ t xs
≈-eat f≈g [] = refl
≈-eat f≈g (x ∷ xs) = ≈ₛ-eatₛ (step f≈g x) xs
≈ₛ-eatₛ ⊥ xs = refl
≈ₛ-eatₛ (next f≈g) xs = ≈-eat f≈g xs
≈ₛ-eatₛ (yield y f≈g) xs = cong (Maybe.map _) (≈-eat f≈g xs)

≈-eat∞ : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → ∀ xs → Bisim (eat∞ f xs) (eat∞ g xs)
≈ₛ-eatₛ∞ : {s : Step X Y d₁} {t : Step X Y d₂} → s ≈ₛ t → ∀ xs → Bisim (eatₛ∞ s xs) (eatₛ∞ t xs)
≈-eat∞ f≈g (x ∷ xs) = ≈ₛ-eatₛ∞ (step f≈g x) xs
≈ₛ-eatₛ∞ ⊥ xs = []
≈ₛ-eatₛ∞ (next f≈g) xs = ≈-eat∞ f≈g (♭ xs)
≈ₛ-eatₛ∞ (yield y f≈g) xs = y ∷ ♯ ≈-eat∞ f≈g (♭ xs)

≈-cast : .{eq : d₁ ≡ d₂} {f : IST X Y d₁} → cast eq f ≈ f
≈ₛ-castₛ : .{eq : d₁ ≡ d₂} {s : Step X Y d₁} → castₛ eq s ≈ₛ s
same-d (≈-cast {d₁ = d₁} {d₂ = d₂} {eq = eq}) = recompute (d₂ ≟ d₁) (sym eq)
step ≈-cast x = ≈ₛ-castₛ
≈ₛ-castₛ {d₂ = zero} {s = ⊥} = ⊥
≈ₛ-castₛ {d₂ = zero} {s = yield y f} = ≈ₛ-refl
≈ₛ-castₛ {d₂ = suc d₂} {s = ⊥} = ⊥
≈ₛ-castₛ {d₂ = suc d₂} {s = next f} = next ≈-cast

module ≈-Reasoning where

  infix 1 begin_
  infixr 2 _≈⟨_⟩_
  infix 3 _∎

  begin_ : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → f ≈ g
  begin p = p

  _≈⟨_⟩_ : (f : IST X Y d₁) {g : IST X Y d₂} {h : IST X Y d₃} → f ≈ g → g ≈ h → f ≈ h
  _ ≈⟨ p ⟩ q = ≈-trans p q

  _∎ : (f : IST X Y d) → f ≈ f
  _ ∎ = ≈-refl

--------------------------------------------------------------------------------
-- Less defined

infix 4 _⊑_ _⊑ₛ_

record _⊑_ (f : IST X Y d₁) (g : IST X Y d₂) : Set
data _⊑ₛ_ {X Y} : Step X Y d₁ → Step X Y d₂ → Set

record _⊑_ {X Y d₁ d₂} f g where
  coinductive
  field
    same-d : d₁ ≡ d₂
    step : ∀ (x : X) → step f x ⊑ₛ step g x

data _⊑ₛ_ {X Y} where
  ⊥ₗ : ∀ {d₁ d₂} {s : Step X Y d₂} → ⊥ {d = d₁} ⊑ₛ s
  next : {f : IST X Y d₁} {g : IST X Y d₂} (p : f ⊑ g) → next f ⊑ₛ next g
  yield : ∀ x {f g} (p : f ⊑ g) → yield x f ⊑ₛ yield x g

open _⊑_ public

≈-to-⊑ : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → f ⊑ g
≈ₛ-to-⊑ₛ : {s : Step X Y d₁} {t : Step X Y d₂} → s ≈ₛ t → s ⊑ₛ t
same-d (≈-to-⊑ f≈g) = same-d f≈g
step (≈-to-⊑ f≈g) x = ≈ₛ-to-⊑ₛ (step f≈g x)
≈ₛ-to-⊑ₛ ⊥ = ⊥ₗ
≈ₛ-to-⊑ₛ (next f≈g) = next (≈-to-⊑ f≈g)
≈ₛ-to-⊑ₛ (yield x f≈g) = yield x (≈-to-⊑ f≈g)

⊑-refl : {f : IST X Y d} → f ⊑ f
⊑ₛ-refl : {s : Step X Y d} → s ⊑ₛ s
⊑-refl = ≈-to-⊑ ≈-refl
⊑ₛ-refl = ≈ₛ-to-⊑ₛ ≈ₛ-refl

⊑-trans : {f : IST X Y d₁} {g : IST X Y d₂} {h : IST X Y d₃} → f ⊑ g → g ⊑ h → f ⊑ h
⊑ₛ-trans : {s : Step X Y d₁} {t : Step X Y d₂} {u : Step X Y d₃} → s ⊑ₛ t → t ⊑ₛ u → s ⊑ₛ u
same-d (⊑-trans f⊑g g⊑h) = trans (same-d f⊑g) (same-d g⊑h)
step (⊑-trans f⊑g g⊑h) x = ⊑ₛ-trans (step f⊑g x) (step g⊑h x)
⊑ₛ-trans ⊥ₗ _ = ⊥ₗ
⊑ₛ-trans (next f⊑g) (next g⊑h) = next (⊑-trans f⊑g g⊑h)
⊑ₛ-trans (yield x f⊑g) (yield .x g⊑h) = yield x (⊑-trans f⊑g g⊑h)

module ⊑-Reasoning where

  infix 1 begin_
  infixr 2 _≈⟨_⟩_ _⊑⟨_⟩_
  infix 3 _∎

  begin_ : {f : IST X Y d₁} {g : IST X Y d₂} → f ⊑ g → f ⊑ g
  begin p = p

  _≈⟨_⟩_ : (f : IST X Y d₁) {g : IST X Y d₂} {h : IST X Y d₃} → f ≈ g → g ⊑ h → f ⊑ h
  _ ≈⟨ p ⟩ q = ⊑-trans (≈-to-⊑ p) q

  _⊑⟨_⟩_ : (f : IST X Y d₁) {g : IST X Y d₂} {h : IST X Y d₃} → f ⊑ g → g ⊑ h → f ⊑ h
  _ ⊑⟨ p ⟩ q = ⊑-trans p q

  _∎ : (f : IST X Y d) → f ⊑ f
  _ ∎ = ⊑-refl

module ⊑ₛ-Reasoning where

  infix 1 begin_
  infixr 2 _≈⟨_⟩_ _⊑⟨_⟩_
  infix 3 _∎

  begin_ : {f : Step X Y d₁} {g : Step X Y d₂} → f ⊑ₛ g → f ⊑ₛ g
  begin p = p

  _≈⟨_⟩_ : (f : Step X Y d₁) {g : Step X Y d₂} {h : Step X Y d₃} → f ≈ₛ g → g ⊑ₛ h → f ⊑ₛ h
  _ ≈⟨ p ⟩ q = ⊑ₛ-trans (≈ₛ-to-⊑ₛ p) q

  _⊑⟨_⟩_ : (f : Step X Y d₁) {g : Step X Y d₂} {h : Step X Y d₃} → f ⊑ₛ g → g ⊑ₛ h → f ⊑ₛ h
  _ ⊑⟨ p ⟩ q = ⊑ₛ-trans p q

  _∎ : (f : Step X Y d) → f ⊑ₛ f
  _ ∎ = ⊑ₛ-refl
