{-# OPTIONS --guardedness #-}

module IIST.Semantics.StateMachine.IST where

open import Data.Maybe.Base as Maybe using ( Maybe; just; nothing )
open import Data.Nat.Base using ( ℕ; zero; suc; pred; _+_ )
open import Data.Nat.Properties using ( +-suc; +-assoc; +-identityʳ; suc-injective )
open import Data.Nat.Instances
open import Data.List.Base using ( List; []; _∷_ )
open import Relation.Binary.Indexed.Heterogeneous.Bundles using ( IndexedSetoid; IndexedPreorder )
open import Relation.Binary.Indexed.Heterogeneous.Structures using ( IsIndexedEquivalence; IsIndexedPreorder )
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using ( recompute )

open import IIST.Common
open import IIST.Syntax
open import Codata.PartialColist using ( Colist⊥; ∞Colist⊥; []; ⊥; _∷_; delay; force ) renaming ( _≈_ to Bisim; _∞≈_ to ∞Bisim )

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
  yield⊥ : Y → Step X Y 0
  yield : Y → IST X Y 0 → Step X Y 0

open IST public

eat : IST X Y d → List X ⇀ List Y
eatₛ : Step X Y d → List X ⇀ List Y
eat f [] = just []
eat f (x ∷ xs) = eatₛ (step f x) xs
eatₛ ⊥ xs = nothing
eatₛ (next f) xs = eat f xs
eatₛ (yield⊥ y) xs = nothing
eatₛ (yield y f) xs = Maybe.map (y ∷_) (eat f xs)

eat∞ : IST X Y d → Colist⊥ X → Colist⊥ Y
eatₛ∞ : Step X Y d → ∞Colist⊥ X → Colist⊥ Y
eat∞ f [] = []
eat∞ f ⊥ = ⊥
eat∞ f (x ∷ xs) = eatₛ∞ (step f x) xs
eatₛ∞ ⊥ xs = ⊥
eatₛ∞ (next f) xs = eat∞ f (force xs)
eatₛ∞ (yield⊥ y) xs = y ∷ delay ⊥
eatₛ∞ (yield y f) xs = y ∷ λ where .force → eat∞ f (force xs)

cast : .(d₁ ≡ d₂) → IST X Y d₁ → IST X Y d₂
castₛ : .(d₁ ≡ d₂) → Step X Y d₁ → Step X Y d₂
step (cast eq f) x = castₛ eq (step f x)
castₛ {d₂ = zero} eq ⊥ = ⊥
castₛ {d₂ = zero} eq (yield⊥ y) = yield⊥ y
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
  yield⊥ : ∀ x → yield⊥ x ≈ₛ yield⊥ x
  yield : ∀ x {f g} (p : f ≈ g) → yield x f ≈ₛ yield x g

open _≈_ public

≈-refl : {f : IST X Y d} → f ≈ f
≈ₛ-refl : {s : Step X Y d} → s ≈ₛ s
same-d ≈-refl = refl
step ≈-refl x = ≈ₛ-refl
≈ₛ-refl {s = ⊥} = ⊥
≈ₛ-refl {s = next f} = next ≈-refl
≈ₛ-refl {s = yield⊥ x} = yield⊥ x
≈ₛ-refl {s = yield x f} = yield x ≈-refl

≈-sym : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → g ≈ f
≈ₛ-sym : {s : Step X Y d₁} {t : Step X Y d₂} → s ≈ₛ t → t ≈ₛ s
same-d (≈-sym f≈g) = sym (same-d f≈g)
step (≈-sym f≈g) x = ≈ₛ-sym (step f≈g x)
≈ₛ-sym ⊥ = ⊥
≈ₛ-sym (next f≈g) = next (≈-sym f≈g)
≈ₛ-sym (yield⊥ x) = yield⊥ x
≈ₛ-sym (yield x f≈g) = yield x (≈-sym f≈g)

≈-trans : {f : IST X Y d₁} {g : IST X Y d₂} {h : IST X Y d₃} → f ≈ g → g ≈ h → f ≈ h
≈ₛ-trans : {s : Step X Y d₁} {t : Step X Y d₂} {u : Step X Y d₃} → s ≈ₛ t → t ≈ₛ u → s ≈ₛ u
same-d (≈-trans f≈g g≈h) = trans (same-d f≈g) (same-d g≈h)
step (≈-trans f≈g g≈h) x = ≈ₛ-trans (step f≈g x) (step g≈h x)
≈ₛ-trans ⊥ ⊥ = ⊥
≈ₛ-trans (next f≈g) (next g≈h) = next (≈-trans f≈g g≈h)
≈ₛ-trans (yield⊥ x) (yield⊥ .x) = yield⊥ x
≈ₛ-trans (yield x f≈g) (yield .x g≈h) = yield x (≈-trans f≈g g≈h)

≈-isIndexedEquivalence : IsIndexedEquivalence (IST X Y) _≈_
≈ₛ-isIndexedEquivalence : IsIndexedEquivalence (Step X Y) _≈ₛ_
≈-isIndexedEquivalence = record { refl = ≈-refl; sym = ≈-sym; trans = ≈-trans }
≈ₛ-isIndexedEquivalence = record { refl = ≈ₛ-refl; sym = ≈ₛ-sym; trans = ≈ₛ-trans }

≈-indexedSetoid : ∀ {X Y} → IndexedSetoid ℕ _ _
≈ₛ-indexedSetoid : ∀ {X Y} → IndexedSetoid ℕ _ _
≈-indexedSetoid {X} {Y} = record { isEquivalence = ≈-isIndexedEquivalence {X} {Y} }
≈ₛ-indexedSetoid {X} {Y} = record { isEquivalence = ≈ₛ-isIndexedEquivalence {X} {Y} }

≈-eat : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → ∀ xs → eat f xs ≡ eat g xs
≈ₛ-eatₛ : {s : Step X Y d₁} {t : Step X Y d₂} → s ≈ₛ t → ∀ xs → eatₛ s xs ≡ eatₛ t xs
≈-eat f≈g [] = refl
≈-eat f≈g (x ∷ xs) = ≈ₛ-eatₛ (step f≈g x) xs
≈ₛ-eatₛ ⊥ xs = refl
≈ₛ-eatₛ (next f≈g) xs = ≈-eat f≈g xs
≈ₛ-eatₛ (yield⊥ _) xs = refl
≈ₛ-eatₛ (yield y f≈g) xs = cong (Maybe.map _) (≈-eat f≈g xs)

≈-eat∞ : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → ∀ xs → Bisim (eat∞ f xs) (eat∞ g xs)
≈ₛ-eatₛ∞ : {s : Step X Y d₁} {t : Step X Y d₂} → s ≈ₛ t → ∀ xs → Bisim (eatₛ∞ s xs) (eatₛ∞ t xs)
≈-eat∞ f≈g [] = []
≈-eat∞ f≈g ⊥ = ⊥
≈-eat∞ f≈g (x ∷ xs) = ≈ₛ-eatₛ∞ (step f≈g x) xs
≈ₛ-eatₛ∞ ⊥ xs = ⊥
≈ₛ-eatₛ∞ (next f≈g) xs = ≈-eat∞ f≈g (force xs)
≈ₛ-eatₛ∞ (yield⊥ y) xs = y ∷ λ where .force → ⊥
≈ₛ-eatₛ∞ (yield y f≈g) xs = y ∷ λ where .force → ≈-eat∞ f≈g (force xs)

≈-eat∞′ : ∀ (f : IST X Y d) {xs ys} → Bisim xs ys → Bisim (eat∞ f xs) (eat∞ f ys)
≈-eatₛ∞′ : ∀ (s : Step X Y d) {xs ys} → ∞Bisim xs ys → Bisim (eatₛ∞ s xs) (eatₛ∞ s ys)
≈-eat∞′ f [] = []
≈-eat∞′ f ⊥ = ⊥
≈-eat∞′ f (x ∷ p) = ≈-eatₛ∞′ (step f x) p
≈-eatₛ∞′ ⊥ p = ⊥
≈-eatₛ∞′ (next f) p = ≈-eat∞′ f (force p)
≈-eatₛ∞′ (yield⊥ y) p = y ∷ λ where .force → ⊥
≈-eatₛ∞′ (yield y f) p = y ∷ λ where .force → ≈-eat∞′ f (force p)

≈-cast : .{eq : d₁ ≡ d₂} {f : IST X Y d₁} → cast eq f ≈ f
≈ₛ-castₛ : .{eq : d₁ ≡ d₂} {s : Step X Y d₁} → castₛ eq s ≈ₛ s
same-d (≈-cast {d₁ = d₁} {d₂ = d₂} {eq = eq}) = recompute (d₂ ≟ d₁) (sym eq)
step ≈-cast x = ≈ₛ-castₛ
≈ₛ-castₛ {d₂ = zero} {s = ⊥} = ⊥
≈ₛ-castₛ {d₂ = zero} {s = yield⊥ y} = yield⊥ y
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
  yield⊥ : ∀ x → yield⊥ x ⊑ₛ yield⊥ x
  yield⊥ₗ : ∀ x {f} → yield⊥ x ⊑ₛ yield x f
  yield : ∀ x {f g} (p : f ⊑ g) → yield x f ⊑ₛ yield x g

open _⊑_ public

≈-to-⊑ : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → f ⊑ g
≈ₛ-to-⊑ₛ : {s : Step X Y d₁} {t : Step X Y d₂} → s ≈ₛ t → s ⊑ₛ t
same-d (≈-to-⊑ f≈g) = same-d f≈g
step (≈-to-⊑ f≈g) x = ≈ₛ-to-⊑ₛ (step f≈g x)
≈ₛ-to-⊑ₛ ⊥ = ⊥ₗ
≈ₛ-to-⊑ₛ (next f≈g) = next (≈-to-⊑ f≈g)
≈ₛ-to-⊑ₛ (yield⊥ x) = yield⊥ x
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
⊑ₛ-trans (yield⊥ x) (yield⊥ .x) = yield⊥ x
⊑ₛ-trans (yield⊥ x) (yield⊥ₗ .x) = yield⊥ₗ x
⊑ₛ-trans (yield⊥ₗ x) (yield .x _) = yield⊥ₗ x
⊑ₛ-trans (yield x f⊑g) (yield .x g⊑h) = yield x (⊑-trans f⊑g g⊑h)

⊑-isIndexedPreorder : IsIndexedPreorder (IST X Y) _≈_ _⊑_
⊑ₛ-isIndexedPreorder : IsIndexedPreorder (Step X Y) _≈ₛ_ _⊑ₛ_
⊑-isIndexedPreorder = record
  { isEquivalence = ≈-isIndexedEquivalence
  ; reflexive = ≈-to-⊑
  ; trans = ⊑-trans
  }
⊑ₛ-isIndexedPreorder = record
  { isEquivalence = ≈ₛ-isIndexedEquivalence
  ; reflexive = ≈ₛ-to-⊑ₛ
  ; trans = ⊑ₛ-trans
  }

⊑-indexedPreorder : ∀ {X Y} → IndexedPreorder ℕ _ _ _
⊑ₛ-indexedPreorder : ∀ {X Y} → IndexedPreorder ℕ _ _ _
⊑-indexedPreorder {X} {Y} = record { isPreorder = ⊑-isIndexedPreorder {X} {Y} }
⊑ₛ-indexedPreorder {X} {Y} = record { isPreorder = ⊑ₛ-isIndexedPreorder {X} {Y} }

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
