{-# OPTIONS --guardedness #-}

module IIST.Semantics.StateMachine.Semantics where

open import Data.Maybe.Base as Maybe using ( Maybe; just; nothing; maybe )
open import Data.Nat.Base using ( ℕ; zero; suc; pred; _+_; _∸_; _⊔_ )
open import Data.Nat.Properties using ( suc-injective; +-suc; +-identityʳ; ⊔-identityʳ; +-comm; +-assoc; ⊔-comm )
open import Data.Nat.Instances
open import Data.List.Base using ( List; []; _∷_ )
open import Data.Product.Base using ( _×_; _,_ )
open import Function.Base using ( case_of_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using ( yes; no; recompute )

open import IIST.Common
open import IIST.Syntax
open import IIST.Semantics.StateMachine.IST

private
  variable
    A X Y Z U V W : Set
    d d₁ d₂ d₃ d₄ : ℕ

  postulate
    sorry : A

--------------------------------------------------------------------------------
-- Semantics

infixr 10 _▸_ _▸ₛ_
infixl 9 _⋙_ _⋙′_ _⋙″_
infixl 8 _⊗_ _⊗ₛ_

id : IST X X 0
step id x = yield x id

shift : X → IST X X 0
step (shift x) y = yield x (shift y)

unshift : {{_ : Eq X}} → X → IST X X 1
step (unshift x) y = case x ≟ y of λ
  { (no _) → ⊥
  ; (yes _) → next id
  }

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → IST X Y 0
step (F-map-fold a f g) x = case f a .to x of λ
  { nothing → ⊥
  ; (just y) → yield y (F-map-fold (g a x) f g)
  }

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → IST Y X 0
step (B-map-fold a f g) y = case f a .from y of λ
  { nothing → ⊥
  ; (just x) → yield x (B-map-fold (g a x) f g)
  }

_⋙_ : IST X Y d₁ → IST Y Z d₂ → IST X Z (d₁ + d₂)
_⋙′_ : Step X Y d₁ → IST Y Z d₂ → Step X Z (d₁ + d₂)
_⋙″_ : IST X Y 0 → Step Y Z d → Step X Z d
step (f ⋙ g) x = step f x ⋙′ g
⊥ ⋙′ g = ⊥
next f ⋙′ g = next (f ⋙ g)
yield⊥ y ⋙′ g = {!   !}
yield y f ⋙′ g = f ⋙″ step g y
f ⋙″ ⊥ = ⊥
f ⋙″ next g = next (f ⋙ g)
f ⋙″ yield⊥ z = yield⊥ z
f ⋙″ yield z g = yield z (f ⋙ g)

later : IST X Y d → IST X Y (suc d)
step (later f) x = next (shift x ⋙ f)

laterN : ∀ n → IST X Y d → IST X Y (n + d)
laterN zero f = f
laterN (suc n) f = later (laterN n f)

-- (y ▸ f) is like (f ⋙ shift y) but fails one-step after if f fails
_▸_ : Y → IST X Y 0 → IST X Y 0
_▸ₛ_ : Y → Step X Y 0 → Step X Y 0
step (y ▸ f) x = y ▸ₛ (step f x)
y ▸ₛ ⊥ = yield⊥ y
y ▸ₛ yield⊥ y' = yield y λ where .step _ → yield⊥ y'
y ▸ₛ yield y' f = yield y (y' ▸ f)

_⊗_ : IST X Y d₁ → IST Z W d₂ → IST (X × Z) (Y × W) (d₁ ⊔ d₂)
_⊗ₛ_ : Step X Y d₁ → Step Z W d₂ → Step (X × Z) (Y × W) (d₁ ⊔ d₂)
step (f ⊗ g) (x , z) = step f x ⊗ₛ step g z
⊥ ⊗ₛ _ = ⊥
_ ⊗ₛ ⊥ = ⊥
next f ⊗ₛ next g = next (f ⊗ g)
next f ⊗ₛ yield w g = castₛ (cong suc (⊔-identityʳ _)) (next (f ⊗ w ▸ g))
yield y f ⊗ₛ next g = next (y ▸ f ⊗ g)
yield y f ⊗ₛ yield w g = yield (y , w) (f ⊗ g)
next f ⊗ₛ yield⊥ w = {!   !}
yield⊥ y ⊗ₛ next g = {!   !}
yield⊥ y ⊗ₛ yield⊥ w = {!   !}
yield⊥ y ⊗ₛ yield w g = {!   !}
yield y x₁ ⊗ₛ yield⊥ w = {!   !}

F⟦_⟧ : (e : E X Y) → IST X Y DF⟦ e ⟧
F⟦ `map-fold a f g ⟧ = F-map-fold a f g
F⟦ `delay x ⟧ = shift x
F⟦ `hasten x ⟧ = unshift x
F⟦ e `⋙ e' ⟧ = F⟦ e ⟧ ⋙ F⟦ e' ⟧
F⟦ e `⊗ e' ⟧ = F⟦ e ⟧ ⊗ F⟦ e' ⟧

B⟦_⟧ : (e : E X Y) → IST Y X DB⟦ e ⟧
B⟦ `map-fold a f g ⟧ = B-map-fold a f g
B⟦ `delay x ⟧ = unshift x
B⟦ `hasten x ⟧ = shift x
B⟦ e `⋙ e' ⟧ = B⟦ e' ⟧ ⋙ B⟦ e ⟧
B⟦ e `⊗ e' ⟧ = B⟦ e ⟧ ⊗ B⟦ e' ⟧

_ : eat id (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : eat (later id) (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (0 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : eat F⟦ `delay 0 ⟧ (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (0 ∷ 0 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : eat F⟦ `hasten 0 ⟧ (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : eat F⟦ `hasten 0 ⟧ (100 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ nothing
_ = refl

_ : eat F⟦ `delay 0 `⊗ `hasten 0 ⟧ ((0 , 0) ∷ (1 , 1) ∷ (2 , 2) ∷ (3 , 3) ∷ [])
  ≡ just ((0 , 1) ∷ (0 , 2) ∷ (1 , 3) ∷ [])
_ = refl

-- --------------------------------------------------------------------------------

-- ⋙-identityₗ : {f : IST X Y d} → id ⋙ f ≈ f
-- ⋙″-identityₗ : {s : Step X Y d} → id ⋙″ s ≈ₛ s
-- same-d ⋙-identityₗ = refl
-- step ⋙-identityₗ x = ⋙″-identityₗ
-- ⋙″-identityₗ {s = ⊥} = ⊥
-- ⋙″-identityₗ {s = next f} = next ⋙-identityₗ
-- ⋙″-identityₗ {s = yield y f} = yield y ⋙-identityₗ

-- ⋙-identityᵣ : {f : IST X Y d} → f ⋙ id ≈ f
-- ⋙′-identityᵣ : {s : Step X Y d} → s ⋙′ id ≈ₛ s
-- same-d ⋙-identityᵣ = +-identityʳ _
-- step ⋙-identityᵣ x = ⋙′-identityᵣ
-- ⋙′-identityᵣ {s = ⊥} = ⊥
-- ⋙′-identityᵣ {s = next f} = next ⋙-identityᵣ
-- ⋙′-identityᵣ {s = yield y f} = yield y ⋙-identityᵣ

-- ⋙-assoc : {f : IST X Y d₁} {g : IST Y Z d₂} {h : IST Z W d₃} → f ⋙ (g ⋙ h) ≈ (f ⋙ g) ⋙ h
-- ⋙′-assoc : {s : Step X Y d₁} {g : IST Y Z d₂} {h : IST Z W d₃} → s ⋙′ (g ⋙ h) ≈ₛ (s ⋙′ g) ⋙′ h
-- ⋙″-assoc₁ : {f : IST X Y 0} {s : Step Y Z d₂} {h : IST Z W d₃} → f ⋙″ (s ⋙′ h) ≈ₛ (f ⋙″ s) ⋙′ h
-- ⋙″-assoc₂ : {f : IST X Y 0} {g : IST Y Z 0} {s : Step Z W d₃} → f ⋙″ (g ⋙″ s) ≈ₛ (f ⋙ g) ⋙″ s
-- ⋙-assoc {d₁ = d₁} .same-d = sym (+-assoc d₁ _ _)
-- step (⋙-assoc {f = f}) x = ⋙′-assoc {s = step f x}
-- ⋙′-assoc {s = ⊥} = ⊥
-- ⋙′-assoc {s = next f} = next ⋙-assoc
-- ⋙′-assoc {s = yield y f} {g} = ⋙″-assoc₁ {s = step g y}
-- ⋙″-assoc₁ {s = ⊥} = ⊥
-- ⋙″-assoc₁ {s = next g} = next ⋙-assoc
-- ⋙″-assoc₁ {s = yield z g} = ⋙″-assoc₂
-- ⋙″-assoc₂ {s = ⊥} = ⊥
-- ⋙″-assoc₂ {s = next h} = next ⋙-assoc
-- ⋙″-assoc₂ {s = yield w h} = yield w ⋙-assoc

-- ≈-cong-⋙ : {f : IST X Y d₁} {f' : IST X Y d₂} {g : IST Y Z d₃} {g' : IST Y Z d₄}
--   → f ≈ f'
--   → g ≈ g'
--   → f ⋙ g ≈ f' ⋙ g'
-- ≈ₛ-cong-⋙′ : {s : Step X Y d₁} {s' : Step X Y d₂} {g : IST Y Z d₃} {g' : IST Y Z d₄}
--   → s ≈ₛ s'
--   → g ≈ g'
--   → s ⋙′ g ≈ₛ s' ⋙′ g'
-- ≈ₛ-cong-⋙″ : {f f' : IST X Y 0} {s : Step Y Z d₁} {s' : Step Y Z d₂}
--   → f ≈ f'
--   → s ≈ₛ s'
--   → f ⋙″ s ≈ₛ f' ⋙″ s'
-- same-d (≈-cong-⋙ f≈f' g≈g') = cong₂ _+_ (same-d f≈f') (same-d g≈g')
-- step (≈-cong-⋙ f≈f' g≈g') x = ≈ₛ-cong-⋙′ (step f≈f' x) g≈g'
-- ≈ₛ-cong-⋙′ ⊥ g≈g' = ⊥
-- ≈ₛ-cong-⋙′ (next f≈f') g≈g' = next (≈-cong-⋙ f≈f' g≈g')
-- ≈ₛ-cong-⋙′ (yield y f≈f') g≈g' = ≈ₛ-cong-⋙″ f≈f' (step g≈g' y)
-- ≈ₛ-cong-⋙″ f≈f' ⊥ = ⊥
-- ≈ₛ-cong-⋙″ f≈f' (next g≈g') = next (≈-cong-⋙ f≈f' g≈g')
-- ≈ₛ-cong-⋙″ f≈f' (yield z g≈g') = yield z (≈-cong-⋙ f≈f' g≈g')

-- ⋙-cast : .{eq₁ : d₁ ≡ d₂} .{eq₂ : d₃ ≡ d₄} {f : IST X Y d₁} {g : IST Y Z d₃}
--   → cast eq₁ f ⋙ cast eq₂ g ≈ cast (cong₂ _+_ eq₁ eq₂) (f ⋙ g)
-- ⋙-cast = ≈-trans (≈-cong-⋙ ≈-cast ≈-cast) (≈-sym ≈-cast)

-- ≈-cong-later : {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → later f ≈ later g
-- same-d (≈-cong-later f≈g) = cong suc (same-d f≈g)
-- step (≈-cong-later f≈g) x = next (≈-cong-⋙ ≈-refl f≈g)

-- ≈-cong-laterN : ∀ n {f : IST X Y d₁} {g : IST X Y d₂} → f ≈ g → laterN n f ≈ laterN n g
-- ≈-cong-laterN zero f≈g = f≈g
-- ≈-cong-laterN (suc n) f≈g = ≈-cong-later (≈-cong-laterN n f≈g)

-- ⋙-later : {f : IST X Y d₁} {g : IST Y Z d₂} → later f ⋙ g ≈ later (f ⋙ g)
-- same-d ⋙-later = refl
-- step ⋙-later x = next (≈-sym ⋙-assoc)

-- ⋙-laterN : ∀ n {f : IST X Y d₁} {g : IST Y Z d₂} → laterN n f ⋙ g ≈ laterN n (f ⋙ g)
-- ⋙-laterN zero = ≈-refl
-- ⋙-laterN (suc n) = ≈-trans ⋙-later (≈-cong-later (⋙-laterN n))

-- laterN-join : ∀ m n {f : IST X Y d} → laterN m (laterN n f) ≈ laterN (m + n) f
-- laterN-join zero _ = ≈-refl
-- laterN-join (suc m) n = ≈-cong-later (laterN-join m n)

-- laterN-cast : ∀ {m n} .(eq : m ≡ n) {f : IST X Y d} → laterN m f ≈ laterN n f
-- laterN-cast {m = zero} {n = zero} eq = ≈-refl
-- laterN-cast {m = suc m} {n = suc n} eq = ≈-cong-later (laterN-cast (suc-injective eq))

-- ≈-cong-▸ : ∀ {y} {f f' : IST X Y 0} → f ≈ f' → y ▸ f ≈ y ▸ f'
-- ≈ₛ-cong-▸ₛ : ∀ {y} {s s' : Step X Y 0} → s ≈ₛ s' → y ▸ₛ s ≈ₛ y ▸ₛ s'
-- same-d (≈-cong-▸ f≈f') = refl
-- step (≈-cong-▸ f≈f') x = ≈ₛ-cong-▸ₛ (step f≈f' x)
-- ≈ₛ-cong-▸ₛ ⊥ = yield _ ≈-refl
-- ≈ₛ-cong-▸ₛ (yield y' f≈f') = yield _ (≈-cong-▸ f≈f')

-- ≈-cong-⊗ : {f : IST X Y d₁} {f' : IST X Y d₂} {g : IST Z W d₃} {g' : IST Z W d₄}
--   → f ≈ f'
--   → g ≈ g'
--   → f ⊗ g ≈ f' ⊗ g'
-- ≈ₛ-cong-⊗ₛ : {s : Step X Y d₁} {s' : Step X Y d₂} {t : Step Z W d₃} {t' : Step Z W d₄}
--   → s ≈ₛ s'
--   → t ≈ₛ t'
--   → s ⊗ₛ t ≈ₛ s' ⊗ₛ t'
-- same-d (≈-cong-⊗ f≈f' g≈g') = cong₂ _⊔_ (same-d f≈f') (same-d g≈g')
-- step (≈-cong-⊗ f≈f' g≈g') (x , z) = ≈ₛ-cong-⊗ₛ (step f≈f' x) (step g≈g' z)
-- ≈ₛ-cong-⊗ₛ ⊥ _ = ⊥
-- ≈ₛ-cong-⊗ₛ (next f≈f') ⊥ = ⊥
-- ≈ₛ-cong-⊗ₛ (yield y f≈f') ⊥ = ⊥
-- ≈ₛ-cong-⊗ₛ (next f≈f') (next g≈g') = next (≈-cong-⊗ f≈f' g≈g')
-- ≈ₛ-cong-⊗ₛ (next f≈f') (yield w g≈g') =
--   next (≈-trans ≈-cast (≈-trans (≈-cong-⊗ f≈f' (≈-cong-▸ g≈g')) (≈-sym ≈-cast)))
-- ≈ₛ-cong-⊗ₛ (yield y f≈f') (next g≈g') = next (≈-cong-⊗ (≈-cong-▸ f≈f') g≈g')
-- ≈ₛ-cong-⊗ₛ (yield y f≈f') (yield w g≈g') = yield (y , w) (≈-cong-⊗ f≈f' g≈g')

-- F∘I≈B : (e : E X Y) → F⟦ I⟦ e ⟧ ⟧ ≈ B⟦ e ⟧
-- F∘I≈B (`map-fold a f g) = helper refl
--   where
--     helper : ∀ {a a'} → a ≡ a' → F⟦ I⟦ `map-fold a f g ⟧ ⟧ ≈ B⟦ `map-fold a' f g ⟧
--     same-d (helper _) = refl
--     step (helper {a} refl) y with f a .from y in eq
--     ... | nothing = ⊥
--     ... | just x = yield x (helper (cong (maybe (g a) a) eq))
-- F∘I≈B (`delay x) = ≈-refl
-- F∘I≈B (`hasten x) = ≈-refl
-- F∘I≈B (e `⋙ e') = ≈-cong-⋙ (F∘I≈B e') (F∘I≈B e)
-- F∘I≈B (e `⊗ e') = ≈-cong-⊗ (F∘I≈B e) (F∘I≈B e')

-- B∘I≈F : (e : E X Y) → B⟦ I⟦ e ⟧ ⟧ ≈ F⟦ e ⟧
-- B∘I≈F (`map-fold a f g) = helper refl
--   where
--     helper : ∀ {a a'} → a ≡ a' → B⟦ I⟦ `map-fold a f g ⟧ ⟧ ≈ F⟦ `map-fold a' f g ⟧
--     same-d (helper _) = refl
--     step (helper {a} refl) x with f a .to x in eq
--     ... | nothing = ⊥
--     ... | just y = yield y (helper (cong (maybe (g a) a) (f a .to→from eq)))
-- B∘I≈F (`delay x) = ≈-refl
-- B∘I≈F (`hasten x) = ≈-refl
-- B∘I≈F (e `⋙ e') = ≈-cong-⋙ (B∘I≈F e) (B∘I≈F e')
-- B∘I≈F (e `⊗ e') = ≈-cong-⊗ (B∘I≈F e) (B∘I≈F e')

-- --------------------------------------------------------------------------------

-- _IsIISTOf_ : IST X Y d₁ → IST Y X d₂ → Set
-- _IsIISTOf_ {d₁ = d₁} {d₂ = d₂} f g = g ⋙ f ⊑ laterN (d₂ + d₁) id

-- shift-IIST : {{_ : Eq X}} (x : X) → shift x IsIISTOf unshift x
-- same-d (shift-IIST x) = refl
-- step (shift-IIST x) x' with x ≟ x'
-- ... | no _ = ⊥ₗ
-- ... | yes refl = next (≈-to-⊑ (≈-trans ⋙-identityₗ (≈-sym ⋙-identityᵣ)))

-- unshift-IIST : {{_ : Eq X}} (x : X) → unshift x IsIISTOf shift x
-- same-d (unshift-IIST x) = refl
-- step (unshift-IIST x) _ with x ≟ x
-- ... | no contra with () ← contra refl
-- ... | yes refl = next ⊑-refl

-- fail⊑ : ∀ {f : IST X Y d} → fail {d = d} ⊑ f
-- same-d fail⊑ = refl
-- step fail⊑ x = ⊥ₗ

-- ⊑-cong-⋙ : {f : IST X Y d₁} {f' : IST X Y d₂} {g : IST Y Z d₃} {g' : IST Y Z d₄}
--   → f ⊑ f'
--   → g ⊑ g'
--   → f ⋙ g ⊑ f' ⋙ g'
-- ⊑ₛ-cong-⋙′ : {s : Step X Y d₁} {s' : Step X Y d₂} {g : IST Y Z d₃} {g' : IST Y Z d₄}
--   → s ⊑ₛ s'
--   → g ⊑ g'
--   → s ⋙′ g ⊑ₛ s' ⋙′ g'
-- ⊑ₛ-cong-⋙″ : {f f' : IST X Y 0} {s : Step Y Z d₁} {s' : Step Y Z d₂}
--   → f ⊑ f'
--   → s ⊑ₛ s'
--   → f ⋙″ s ⊑ₛ f' ⋙″ s'
-- same-d (⊑-cong-⋙ f⊑f' g⊑g') = cong₂ _+_ (same-d f⊑f') (same-d g⊑g')
-- step (⊑-cong-⋙ f⊑f' g⊑g') x = ⊑ₛ-cong-⋙′ (step f⊑f' x) g⊑g'
-- ⊑ₛ-cong-⋙′ ⊥ₗ g⊑g' = ⊥ₗ
-- ⊑ₛ-cong-⋙′ (next f⊑f') g⊑g' = next (⊑-cong-⋙ f⊑f' g⊑g')
-- ⊑ₛ-cong-⋙′ (yield y f⊑f') g⊑g' = ⊑ₛ-cong-⋙″ f⊑f' (step g⊑g' y)
-- ⊑ₛ-cong-⋙″ f⊑f' ⊥ₗ = ⊥ₗ
-- ⊑ₛ-cong-⋙″ f⊑f' (next g⊑g') = next (⊑-cong-⋙ f⊑f' g⊑g')
-- ⊑ₛ-cong-⋙″ f⊑f' (yield z g⊑g') = yield z (⊑-cong-⋙ f⊑f' g⊑g')

-- ⊑-cong-later : {f : IST X Y d₁} {g : IST X Y d₂} → f ⊑ g → later f ⊑ later g
-- ⊑-cong-later f⊑g .same-d = cong suc (same-d f⊑g)
-- step (⊑-cong-later f⊑g) x = next (⊑-cong-⋙ ⊑-refl f⊑g)

-- ⊑-cong-laterN : ∀ n {f : IST X Y d₁} {g : IST X Y d₂} → f ⊑ g → laterN n f ⊑ laterN n g
-- ⊑-cong-laterN zero f⊑g = f⊑g
-- ⊑-cong-laterN (suc n) f⊑g = ⊑-cong-later (⊑-cong-laterN n f⊑g)

-- ⋙-shift : ∀ {f f' : IST X Y 0} {x y}
--   → step f x ≡ yield y f'
--   → f' ⋙ shift y ⊑ shift x ⋙ f
-- ⋙′-shift : ∀ {s : Step X Y 0} {f : IST X Y 0} {x y}
--   → step f x ≡ s
--   → s ⋙′ shift y ⊑ₛ yield y (shift x ⋙ f)
-- same-d (⋙-shift eq) = refl
-- step (⋙-shift eq) x' rewrite eq = ⋙′-shift refl
-- ⋙′-shift {s = ⊥} eq = ⊥ₗ
-- ⋙′-shift {s = yield _ _} eq = yield _ (⋙-shift eq)

-- later-shift-yield : ∀ {f f' : IST X Y 0} {g : IST Y Z d} {x y}
--   → step f x ≡ yield y f'
--   → f' ⋙ (shift y ⋙ g) ⊑ shift x ⋙ (f ⋙ g)
-- later-shift-yield′ : ∀ {s : Step X Y 0} {f : IST X Y 0} {g : IST Y Z d} {x y}
--   → step f x ≡ s
--   → s ⋙′ (shift y ⋙ g) ⊑ₛ shift x ⋙″ (f ⋙″ step g y)
-- same-d (later-shift-yield eq) = refl
-- step (later-shift-yield {f' = f'} {g} {y = y} eq) x' rewrite eq = later-shift-yield′ refl
-- later-shift-yield′ {s = ⊥} eq = ⊥ₗ
-- later-shift-yield′ {s = yield _ _} {g = g} eq = begin
--   _ ⋙″ (shift _ ⋙″ step g _)  ≈⟨ ⋙″-assoc₂ ⟩
--   (_ ⋙ shift _) ⋙″ step g _   ⊑⟨ ⊑ₛ-cong-⋙″ (⋙-shift eq) ⊑ₛ-refl ⟩
--   (shift _ ⋙ _) ⋙″ step g _   ≈⟨ ≈ₛ-sym ⋙″-assoc₂ ⟩
--   shift _ ⋙″ (_ ⋙″ step g _)  ∎
--   where open ⊑ₛ-Reasoning

-- later-shift-next : ∀ {f : IST X Y (suc d₁)} {f' : IST X Y d₁} {g : IST Y Z d₂} {x}
--   → step f x ≡ next f'
--   → f' ⋙ later g ⊑ shift x ⋙ (f ⋙ g)
-- later-shift-next′ : ∀ {s : Step X Y d₁} {f : IST X Y d₁} {g : IST Y Z d₂} {x}
--   → step f x ≡ s
--   → s ⋙′ later g ⊑ₛ next (shift x ⋙ (f ⋙ g))
-- same-d (later-shift-next eq) = +-suc _ _
-- step (later-shift-next eq) x' rewrite eq = later-shift-next′ refl
-- later-shift-next′ {s = ⊥} eq = ⊥ₗ
-- later-shift-next′ {s = next f} eq = next (later-shift-next eq)
-- later-shift-next′ {s = yield y f} eq = next (later-shift-yield eq)

-- ⊑-⋙-later : {f : IST X Y d₁} {g : IST Y Z d₂} → f ⋙ later g ⊑ later (f ⋙ g)
-- ⊑-⋙́′-later : {f : IST X Y d₁} {g : IST Y Z d₂} {s : Step X Y d₁} {x : X}
--   → step f x ≡ s
--   → s ⋙′ later g ⊑ₛ next (shift x ⋙ (f ⋙ g))
-- same-d ⊑-⋙-later = +-suc _ _
-- step ⊑-⋙-later x = ⊑-⋙́′-later refl
-- ⊑-⋙́′-later {s = ⊥} eq = ⊥ₗ
-- ⊑-⋙́′-later {s = next _} eq = next (later-shift-next eq)
-- ⊑-⋙́′-later {s = yield _ _} eq = next (later-shift-yield eq)

-- ⊑-⋙-laterN : ∀ n {f : IST X Y d₁} {g : IST Y Z d₂} → f ⋙ laterN n g ⊑ laterN n (f ⋙ g)
-- ⊑-⋙-laterN zero = ⊑-refl
-- ⊑-⋙-laterN (suc n) = ⊑-trans ⊑-⋙-later (⊑-cong-later (⊑-⋙-laterN n))

-- ⊑-cong-▸ : ∀ {y} {f f' : IST X Y 0} → f ⊑ f' → y ▸ f ⊑ y ▸ f'
-- ⊑ₛ-cong-▸ₛ : ∀ {y} {s s' : Step X Y 0} → s ⊑ₛ s' → y ▸ₛ s ⊑ₛ y ▸ₛ s'
-- same-d (⊑-cong-▸ f⊑f') = refl
-- step (⊑-cong-▸ f⊑f') x = ⊑ₛ-cong-▸ₛ (step f⊑f' x)
-- ⊑ₛ-cong-▸ₛ {s' = ⊥} ⊥ₗ = ⊑ₛ-refl
-- ⊑ₛ-cong-▸ₛ {s' = yield _ _} ⊥ₗ = yield _ fail⊑
-- ⊑ₛ-cong-▸ₛ (yield y f⊑f') = yield _ (⊑-cong-▸ f⊑f')

-- ⊑-cong-⊗ : {f : IST X Y d₁} {f' : IST X Y d₂} {g : IST Z W d₃} {g' : IST Z W d₄}
--   → f ⊑ f'
--   → g ⊑ g'
--   → f ⊗ g ⊑ f' ⊗ g'
-- ⊑ₛ-cong-⊗ₛ : {s : Step X Y d₁} {s' : Step X Y d₂} {t : Step Z W d₃} {t' : Step Z W d₄}
--   → s ⊑ₛ s'
--   → t ⊑ₛ t'
--   → s ⊗ₛ t ⊑ₛ s' ⊗ₛ t'
-- same-d (⊑-cong-⊗ f⊑f' g⊑g') = cong₂ _⊔_ (same-d f⊑f') (same-d g⊑g')
-- step (⊑-cong-⊗ f⊑f' g⊑g') (x , z) = ⊑ₛ-cong-⊗ₛ (step f⊑f' x) (step g⊑g' z)
-- ⊑ₛ-cong-⊗ₛ ⊥ₗ _ = ⊥ₗ
-- ⊑ₛ-cong-⊗ₛ (next f⊑f') ⊥ₗ = ⊥ₗ
-- ⊑ₛ-cong-⊗ₛ (yield y f⊑f') ⊥ₗ = ⊥ₗ
-- ⊑ₛ-cong-⊗ₛ (next f⊑f') (next g⊑g') = next (⊑-cong-⊗ f⊑f' g⊑g')
-- ⊑ₛ-cong-⊗ₛ (next f⊑f') (yield w g⊑g') =
--   next (⊑-trans (≈-to-⊑ ≈-cast) (⊑-trans (⊑-cong-⊗ f⊑f' (⊑-cong-▸ g⊑g')) (≈-to-⊑ (≈-sym ≈-cast))))
-- ⊑ₛ-cong-⊗ₛ (yield y f⊑f') (next g⊑g') = next (⊑-cong-⊗ (⊑-cong-▸ f⊑f') g⊑g')
-- ⊑ₛ-cong-⊗ₛ (yield y f⊑f') (yield w g⊑g') = yield (y , w) (⊑-cong-⊗ f⊑f' g⊑g')

-- ⋙-IIST : ∀ {d₁ d₂ d₃ d₄} {f : IST X Y d₁} {f' : IST Y X d₂} {g : IST Y Z d₃} {g' : IST Z Y d₄}
--   → f' IsIISTOf f
--   → g' IsIISTOf g
--   → (g' ⋙ f') IsIISTOf (f ⋙ g)
-- ⋙-IIST {d₁ = d₁} {d₂} {d₃} {d₄} {f} {f'} {g} {g'} f-inv-f' g-inv-g' = begin
--   (f ⋙ g) ⋙ (g' ⋙ f')                  ≈⟨ ≈-sym ⋙-assoc ⟩
--   f ⋙ (g ⋙ (g' ⋙ f'))                  ≈⟨ ≈-cong-⋙ ≈-refl ⋙-assoc ⟩
--   f ⋙ ((g ⋙ g') ⋙ f')                  ⊑⟨ ⊑-cong-⋙ ⊑-refl (⊑-cong-⋙ g-inv-g' ⊑-refl) ⟩
--   f ⋙ (laterN (d₃ + d₄) id ⋙ f')        ≈⟨ ≈-cong-⋙ ≈-refl (⋙-laterN (d₃ + d₄)) ⟩
--   f ⋙ laterN (d₃ + d₄) (id ⋙ f')        ≈⟨ ≈-cong-⋙ ≈-refl (≈-cong-laterN (d₃ + d₄) ⋙-identityₗ) ⟩
--   f ⋙ laterN (d₃ + d₄) f'                ⊑⟨ ⊑-⋙-laterN (d₃ + d₄) ⟩
--   laterN (d₃ + d₄) (f ⋙ f')              ⊑⟨ ⊑-cong-laterN (d₃ + d₄) f-inv-f' ⟩
--   laterN (d₃ + d₄) (laterN (d₁ + d₂) id)  ≈⟨ laterN-join (d₃ + d₄) (d₁ + d₂) ⟩
--   laterN ((d₃ + d₄) + (d₁ + d₂)) id       ≈⟨ laterN-cast (h d₃ d₄ d₁ d₂) ⟩
--   laterN ((d₁ + d₃) + (d₄ + d₂)) id       ∎
--   where
--     open ⊑-Reasoning
--     open import Data.Nat.Tactic.RingSolver

--     h : ∀ m n o p → (m + n) + (o + p) ≡ (o + m) + (n + p)
--     h = solve-∀

-- ⊗-⋙-interchange : ∀ {d₁ d₂ d₃ d₄} {f : IST X Y d₁} {f' : IST Y Z d₂} {g : IST U V d₃} {g' : IST V W d₄}
--   → (f ⊗ g) ⋙ (f' ⊗ g') ⊑ (laterN (d₃ ∸ d₁) f ⋙ laterN (d₄ ∸ d₂) f') ⊗ (laterN (d₁ ∸ d₃) g ⋙ laterN (d₂ ∸ d₄) g')
-- ⊗-⋙-interchange = sorry

-- id⊗id : id {X} ⊗ id {Y} ≈ id {X × Y}
-- same-d id⊗id = refl
-- step id⊗id (x , y) = yield (x , y) id⊗id

-- ⊗-later-id : later (id {X}) ⊗ later (id {Y}) ≈ later (id ⊗ id)
-- same-d ⊗-later-id = refl
-- step ⊗-later-id (x , y) = next sorry

-- ⊗-laterN-id : ∀ n → laterN n (id {X}) ⊗ laterN n (id {Y}) ≈ laterN n (id ⊗ id)
-- ⊗-laterN-id zero = ≈-refl
-- ⊗-laterN-id (suc n) = sorry

-- ⊗-IIST : ∀ {d₁ d₂ d₃ d₄} {f : IST X Y d₁} {f' : IST Y X d₂} {g : IST Z W d₃} {g' : IST W Z d₄}
--   → f' IsIISTOf f
--   → g' IsIISTOf g
--   → (f' ⊗ g') IsIISTOf (f ⊗ g)
-- ⊗-IIST {d₁ = d₁} {d₂} {d₃} {d₄} {f} {f'} {g} {g'} f-inv-f' g-inv-g' =
--   begin
--     (f ⊗ g) ⋙ (f' ⊗ g')
--   ⊑⟨ ⊗-⋙-interchange ⟩
--     (laterN (d₃ ∸ d₁) f ⋙ laterN (d₄ ∸ d₂) f') ⊗ (laterN (d₁ ∸ d₃) g ⋙ laterN (d₂ ∸ d₄) g')
--   ⊑⟨ ⊑-cong-⊗ (h₂ f-inv-f') (h₂ g-inv-g') ⟩
--     laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) id ⊗ laterN ((d₃ ⊔ d₁) + (d₄ ⊔ d₂)) id
--   ≈⟨ ≈-cong-⊗ ≈-refl (laterN-cast (cong₂ _+_ (⊔-comm d₃ _) (⊔-comm d₄ _))) ⟩
--     laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) id ⊗ laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) id
--   ≈⟨ ⊗-laterN-id ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) ⟩
--     laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) (id ⊗ id)
--   ≈⟨ ≈-cong-laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) id⊗id ⟩
--     laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) id
--   ∎
--   where
--     open ⊑-Reasoning

--     h₁ : ∀ m n o p → (m ∸ n) + (o ∸ p) + (n + p) ≡ (n ⊔ m) + (p ⊔ o)
--     h₁ m n o p = sorry

--     h₂ : ∀ {d₁ d₂ d₃ d₄} {f : IST X Y d₁} {f' : IST Y X d₂}
--       → f' IsIISTOf f
--       → laterN (d₃ ∸ d₁) f ⋙ laterN (d₄ ∸ d₂) f' ⊑ laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) id
--     h₂ {d₁ = d₁} {d₂} {d₃} {d₄} {f} {f'} f-inv-f' = begin
--       laterN (d₃ ∸ d₁) f ⋙ laterN (d₄ ∸ d₂) f'             ≈⟨ ⋙-laterN (d₃ ∸ d₁) ⟩
--       laterN (d₃ ∸ d₁) (f ⋙ laterN (d₄ ∸ d₂) f')           ⊑⟨ ⊑-cong-laterN (d₃ ∸ d₁) (⊑-⋙-laterN (d₄ ∸ d₂)) ⟩
--       laterN (d₃ ∸ d₁) (laterN (d₄ ∸ d₂) (f ⋙ f'))         ≈⟨ laterN-join (d₃ ∸ d₁) (d₄ ∸ d₂) ⟩
--       laterN ((d₃ ∸ d₁) + (d₄ ∸ d₂)) (f ⋙ f')              ⊑⟨ ⊑-cong-laterN ((d₃ ∸ d₁) + (d₄ ∸ d₂)) f-inv-f' ⟩
--       laterN ((d₃ ∸ d₁) + (d₄ ∸ d₂)) (laterN (d₁ + d₂) id)  ≈⟨ laterN-join ((d₃ ∸ d₁) + (d₄ ∸ d₂)) (d₁ + d₂) ⟩
--       laterN ((d₃ ∸ d₁) + (d₄ ∸ d₂) + (d₁ + d₂)) id         ≈⟨ laterN-cast (h₁ d₃ d₁ d₄ d₂) ⟩
--       laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) id                     ∎

-- F-IIST : (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
-- F-IIST (`map-fold a f g) = helper a
--   where
--     helper : ∀ a → (B⟦ `map-fold a f g ⟧ ⋙ F⟦ `map-fold a f g ⟧) ⊑ id
--     helper a .same-d = refl
--     helper a .step y with f a .from y in eq
--     ... | nothing = ⊥ₗ
--     ... | just x rewrite f a .from→to eq = yield y (helper (g a x))
-- F-IIST (`delay x) = shift-IIST x
-- F-IIST (`hasten x) = unshift-IIST x
-- F-IIST (e `⋙ e') = ⋙-IIST (F-IIST e') (F-IIST e)
-- F-IIST (e `⊗ e') = ⊗-IIST (F-IIST e) (F-IIST e')

-- B-IIST : (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
-- B-IIST (`map-fold a f g) = helper a
--   where
--     helper : ∀ a → (F⟦ `map-fold a f g ⟧ ⋙ B⟦ `map-fold a f g ⟧) ⊑ id
--     helper a .same-d = refl
--     helper a .step x with f a .to x in eq
--     ... | nothing = ⊥ₗ
--     ... | just y rewrite f a .to→from eq = yield x (helper (g a x))
-- B-IIST (`delay x) = unshift-IIST x
-- B-IIST (`hasten x) = shift-IIST x
-- B-IIST (e `⋙ e') = ⋙-IIST (B-IIST e) (B-IIST e')
-- B-IIST (e `⊗ e') = ⊗-IIST (B-IIST e) (B-IIST e')
