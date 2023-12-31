{-# OPTIONS --guardedness #-}

module IIST.Experiment.DefinitionallyIncremental where

open import Codata.Musical.Notation
open import Codata.Musical.Colist.Base using ( Colist; []; _∷_ )
open import Codata.Musical.Colist.Bisimilarity using ( []; _∷_ ) renaming ( _≈_ to Bisim )
open import Codata.Musical.Stream using ( Stream; _∷_ )
open import Data.Maybe.Base as Maybe using ( Maybe; just; nothing )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_; NonZero )
open import Data.Nat.Properties using ( +-suc; +-identityʳ; ⊔-identityʳ; +-comm )
open import Data.Nat.Instances
open import Data.List.Base using ( List; []; _∷_ )
open import Data.Product.Base using ( Σ-syntax; _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong; subst )
open import Relation.Nullary using ( yes; no )

open import IIST.Common
open import IIST.Syntax

private
  variable
    A X Y Z W : Set

--------------------------------------------------------------------------------
-- Definitionally d-incremental sequence transformation

mutual

  record IST (X Y : Set) (d : ℕ) : Set where
    coinductive
    field
      step : X → Step X Y d

  data Step (X Y : Set) : ℕ → Set where
    ⊥ : ∀ {d} → Step X Y d
    next : ∀ {d} → IST X Y d → Step X Y (suc d)
    yield : Y → IST X Y 0 → Step X Y 0

open IST

eat : ∀ {d} → IST X Y d → List X → Maybe (List Y)
eat f [] = just []
eat f (x ∷ xs) with f .step x
... | ⊥ = nothing
... | next f' = eat f' xs
... | yield y f' = Maybe.map (y ∷_) (eat f' xs)

eat∞ : ∀ {d} → IST X Y d → Stream X → Colist Y
eat∞ f (x ∷ xs) with f .step x
... | ⊥ = []
... | next f' = eat∞ f' (♭ xs)
... | yield y f' = y ∷ ♯ eat∞ f' (♭ xs)

--------------------------------------------------------------------------------
-- Semantics

id : IST X X 0
id .step x = yield x id

shift : X → IST X X 0
shift x .step y = yield x (shift y)

unshift : {{_ : Eq X}} → X → IST X X 1
unshift x .step y with x ≟ y
... | no _ = ⊥
... | yes _ = next id

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → IST X Y 0
F-map-fold a f g .step x with f a .to x
... | nothing = ⊥
... | just y = yield y (F-map-fold (g a x) f g)

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → IST Y X 0
B-map-fold a f g .step y with f a .from y
... | nothing = ⊥
... | just x = yield x (B-map-fold (g a x) f g)

_∙_ : ∀ {d d'} → IST X Y d → IST Y Z d' → IST X Z (d + d')
(f ∙ g) .step x with f .step x
... | ⊥ = ⊥
... | next f' = next (f' ∙ g)
... | yield y f' with g .step y
...   | ⊥ = ⊥
...   | next g' = next (f' ∙ g')
...   | yield z g' = yield z (f' ∙ g')

later : ∀ {d} → IST X Y d → IST X Y (suc d)
later f .step x = next (shift x ∙ f)

laterN : ∀ n {d} → IST X Y d → IST X Y (n + d)
laterN zero f = f
laterN (suc n) f = later (laterN n f)

_∥_ : ∀ {d d'} → IST X Y d → IST Z W d' → IST (X × Z) (Y × W) (d ⊔ d')
(f ∥ g) .step (x , z) with f .step x | g .step z
... | ⊥ | _ = ⊥
... | _ | ⊥ = ⊥
... | next f' | next g' = next (f' ∥ g')
... | next {d} f' | yield _ _ = next (subst (IST _ _) (⊔-identityʳ d) (f' ∥ (shift z ∙ g)))
... | yield _ _  | next g' = next ((shift x ∙ f) ∥ g')
... | yield y f' | yield w g' = yield (y , w) (f' ∥ g')

F⟦_⟧ : (e : E X Y) → IST X Y DF⟦ e ⟧
F⟦ map-fold a f g ⟧ = F-map-fold a f g
F⟦ delay x ⟧ = shift x
F⟦ hasten x ⟧ = unshift x
F⟦ e ⟫ e' ⟧ = F⟦ e ⟧ ∙ F⟦ e' ⟧
F⟦ e ⊗ e' ⟧ = F⟦ e ⟧ ∥ F⟦ e' ⟧

B⟦_⟧ : (e : E X Y) → IST Y X DB⟦ e ⟧
B⟦ map-fold a f g ⟧ = B-map-fold a f g
B⟦ delay x ⟧ = unshift x
B⟦ hasten x ⟧ = shift x
B⟦ e ⟫ e' ⟧ = B⟦ e' ⟧ ∙ B⟦ e ⟧
B⟦ e ⊗ e' ⟧ = B⟦ e ⟧ ∥ B⟦ e' ⟧

_ : eat id (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : eat (later id) (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (0 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : eat F⟦ delay 0 ⊗ hasten 0 ⟧ ((0 , 0) ∷ (1 , 1) ∷ (2 , 2) ∷ (3 , 3) ∷ [])
  ≡ just ((0 , 1) ∷ (0 , 2) ∷ (1 , 3) ∷ [])
_ = refl

--------------------------------------------------------------------------------
-- Bisimulation

mutual

  record _≈_ {d d'} (f : IST X Y d) (g : IST X Y d') : Set where
    coinductive
    field
      step : ∀ (x : X) → step f x Step≈ step g x

  data _Step≈_ {X Y} : ∀ {d d'} → Step X Y d → Step X Y d' → Set where
    ⊥ : ∀ {d d'} → ⊥ {d = d} Step≈ ⊥ {d = d'}
    next : ∀ {d d'} {f : IST X Y d} {g : IST X Y d'}
      → f ≈ g
      → next f Step≈ next g
    yield : ∀ {x y f g}
      → x ≡ y
      → f ≈ g
      → yield x f Step≈ yield y g

open _≈_

≈-refl : ∀ {d} {f : IST X Y d} → f ≈ f
≈-refl {f = f} .step x with f .step x
... | ⊥ = ⊥
... | next f' = next ≈-refl
... | yield y f' = yield refl ≈-refl

≈-sym : ∀ {d d'} {f : IST X Y d} {g : IST X Y d'} → f ≈ g → g ≈ f
≈-sym {f = f} {g} f≈g .step x with f .step x | g .step x | f≈g .step x
... | ⊥ | ⊥ | ⊥ = ⊥
... | next _ | next _ | next f'≈g' = next (≈-sym f'≈g')
... | yield _ _ | yield _ _ | yield refl f'≈g' = yield refl (≈-sym f'≈g')

≈-trans : ∀ {d₁ d₂ d₃} {f : IST X Y d₁} {g : IST X Y d₂} {h : IST X Y d₃}
  → f ≈ g
  → g ≈ h
  → f ≈ g
≈-trans {f = f} {g} {h} f≈g g≈h .step x
  with f .step x | g .step x | h .step x | f≈g .step x | g≈h .step x
... | ⊥ | ⊥ | ⊥ | ⊥ | ⊥ = ⊥
... | next _ | next _ | next _ | next f'≈g' | next g'≈h' =
      next (≈-trans f'≈g' g'≈h')
... | yield _ _ | yield _ _ | yield _ _ | yield refl f'≈g' | yield refl g'≈h' =
      yield refl (≈-trans f'≈g' g'≈h')

≈-eat : ∀ {d d'} {f : IST X Y d} {g : IST X Y d'}
  → f ≈ g
  → ∀ xs → eat f xs ≡ eat g xs
≈-eat f≈g [] = refl
≈-eat {f = f} {g} f≈g (x ∷ xs) with f .step x | g .step x | f≈g .step x
... | ⊥ | ⊥ | ⊥ = refl
... | next _ | next _ | next f'≈g' = ≈-eat f'≈g' xs
... | yield _ _ | yield _ _ | yield refl f'≈g' = cong (Maybe.map _) (≈-eat f'≈g' xs)

≈-eat∞ : ∀ {d d'} {f : IST X Y d} {g : IST X Y d'}
  → f ≈ g
  → ∀ xs → Bisim (eat∞ f xs) (eat∞ g xs)
≈-eat∞ {f = f} {g} f≈g (x ∷ xs) with f .step x | g .step x | f≈g .step x
... | ⊥ | ⊥ | ⊥ = []
... | next _ | next _ | next f'≈g' = ≈-eat∞ f'≈g' (♭ xs)
... | yield y _ | yield _ _ | yield refl f'≈g' = y ∷ ♯ ≈-eat∞ f'≈g' (♭ xs)

≈-cong-subst : ∀ {d₁ d₁' d₂ d₂'} {f : IST X Y d₁} {g : IST X Y d₂}
  → (p : d₁ ≡ d₁') (q : d₂ ≡ d₂')
  → f ≈ g
  → subst (IST X Y) p f ≈ subst (IST X Y) q g
≈-cong-subst refl refl p = p

--------------------------------------------------------------------------------

≈-cong-∙ : ∀ {d₁ d₁' d₂ d₂'}
  → {f : IST X Y d₁} {f' : IST X Y d₁'} {g : IST Y Z d₂} {g' : IST Y Z d₂'}
  → f ≈ f'
  → g ≈ g'
  → (f ∙ g) ≈ (f' ∙ g')
≈-cong-∙ {f = f} {f'} {g} {g'} f≈f' g≈g' .step x
  with f .step x | f' .step x | f≈f' .step x
... | ⊥ | ⊥ | ⊥ = ⊥
... | next _ | next _ | next f≈f' = next (≈-cong-∙ f≈f' g≈g')
... | yield y _ | yield _ _ | yield refl f≈f' with g .step y | g' .step y | g≈g' .step y
...   | ⊥ | ⊥ | ⊥ = ⊥
...   | next _ | next _ | next g≈g' = next (≈-cong-∙ f≈f' g≈g')
...   | yield _ _ | yield _ _ | yield refl g≈g' = yield refl (≈-cong-∙ f≈f' g≈g')

≈-cong-∥ : ∀ {d₁ d₁' d₂ d₂'}
  → {f : IST X Y d₁} {f' : IST X Y d₁'} {g : IST Z W d₂} {g' : IST Z W d₂'}
  → f ≈ f'
  → g ≈ g'
  → (f ∥ g) ≈ (f' ∥ g')
≈-cong-∥ {f = f} {f'} {g} {g'} f≈f' g≈g' .step (x , z)
  with f .step x | f' .step x | g .step z | g' .step z | f≈f' .step x | g≈g' .step z
... | ⊥ | ⊥ | _ | _ | ⊥ | _ = ⊥
... | next _ | next _ | ⊥ | ⊥ | _ | ⊥ = ⊥
... | yield _ _ | yield _ _ | ⊥ | ⊥ | _ | ⊥ = ⊥
... | next _ | next _ | next _ | next _ | next f≈f' | next g≈g' =
      next (≈-cong-∥ f≈f' g≈g')
... | next f | next f' | yield _ _ | yield _ _ | next {d} {d'} f≈f' | yield refl _ =
      next (≈-cong-subst (⊔-identityʳ d) (⊔-identityʳ d') (≈-cong-∥ f≈f' (≈-cong-∙ ≈-refl g≈g')))
... | yield _ _ | yield _ _ | next _ | next _ | yield refl _ | next g≈g' =
      next (≈-cong-∥ (≈-cong-∙ (≈-refl {f = shift x}) f≈f') g≈g')
... | yield _ _ | yield _ _ | yield _ _ | yield _ _ | yield refl f≈f' | yield refl g≈g' =
      yield refl (≈-cong-∥ f≈f' g≈g')

F∘I≈B : ∀ (e : E X Y) → F⟦ I⟦ e ⟧ ⟧ ≈ B⟦ e ⟧
F∘I≈B (map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → F⟦ I⟦ map-fold a f g ⟧ ⟧ ≈ B⟦ map-fold a' f g ⟧
    helper {a} refl .step y with f a .from y in eq
    ... | nothing = ⊥
    ... | just x = yield refl (helper (cong (Maybe.maybe (g a) a) eq))
F∘I≈B (delay x) = ≈-refl
F∘I≈B (hasten x) = ≈-refl
F∘I≈B (e ⟫ e') = ≈-cong-∙ (F∘I≈B e') (F∘I≈B e)
F∘I≈B (e ⊗ e') = ≈-cong-∥ (F∘I≈B e) (F∘I≈B e')

B∘I≈F : ∀ (e : E X Y) → B⟦ I⟦ e ⟧ ⟧ ≈ F⟦ e ⟧
B∘I≈F (map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → B⟦ I⟦ map-fold a f g ⟧ ⟧ ≈ F⟦ map-fold a' f g ⟧
    helper {a} refl .step x with f a .to x in eq
    ... | nothing = ⊥
    ... | just y = yield refl (helper (cong (Maybe.maybe (g a) a) (f a .to→from eq)))
B∘I≈F (delay x) = ≈-refl
B∘I≈F (hasten x) = ≈-refl
B∘I≈F (e ⟫ e') = ≈-cong-∙ (B∘I≈F e) (B∘I≈F e')
B∘I≈F (e ⊗ e') = ≈-cong-∥ (B∘I≈F e) (B∘I≈F e')

--------------------------------------------------------------------------------
-- More defined

mutual

  record _⊑_ {d d'} (f : IST X Y d) (g : IST X Y d') : Set where
    coinductive
    field
      step : ∀ (x : X) → step f x Step⊑ step g x

  data _Step⊑_ {X Y} : ∀ {d d'} → Step X Y d → Step X Y d' → Set where
    ⊥ₗ : ∀ {d d'} {s : Step X Y d'} → ⊥ {d = d} Step⊑ s
    next : ∀ {d d'} {f : IST X Y d} {g : IST X Y d'}
      → f ⊑ g
      → next f Step⊑ next g
    yield : ∀ {x y f g}
      → x ≡ y
      → f ⊑ g
      → yield x f Step⊑ yield y g

open _⊑_

≈-to-⊑ : ∀ {d d'} {f : IST X Y d} {g : IST X Y d'}
  → f ≈ g
  → f ⊑ g
≈-to-⊑ {f = f} {g} f≈g .step x with f .step x | g .step x | f≈g .step x
... | ⊥ | ⊥ | ⊥ = ⊥ₗ
... | next _ | next _ | next f'≈g' = next (≈-to-⊑ f'≈g')
... | yield _ _ | yield _ _ | yield refl f'≈g' = yield refl (≈-to-⊑ f'≈g')

⊑-refl : ∀ {d} {f : IST X Y d} → f ⊑ f
⊑-refl {f = f} .step x with f .step x
... | ⊥ = ⊥ₗ
... | next f' = next ⊑-refl
... | yield y f' = yield refl ⊑-refl

⊑-trans : ∀ {d₁ d₂ d₃} {f : IST X Y d₁} {g : IST X Y d₂} {h : IST X Y d₃}
  → f ⊑ g
  → g ⊑ h
  → f ⊑ h
⊑-trans {f = f} {g} {h} f⊑g g⊑h .step x
  with f .step x | g .step x | h .step x | f⊑g .step x | g⊑h .step x
... | ⊥ | _ | _ | _ | _ = ⊥ₗ
... | next _ | next _ | next _ | next f'⊑g' | next g'⊑h' =
      next (⊑-trans f'⊑g' g'⊑h')
... | yield _ _ | yield _ _ | yield _ _ | yield refl f'⊑g' | yield refl g'⊑h' =
      yield refl (⊑-trans f'⊑g' g'⊑h')

⊑-cong-subst : ∀ {d₁ d₁' d₂ d₂'} {f : IST X Y d₁} {g : IST X Y d₂}
  → (p : d₁ ≡ d₁') (q : d₂ ≡ d₂')
  → f ⊑ g
  → subst (IST X Y) p f ⊑ subst (IST X Y) q g
⊑-cong-subst refl refl p = p

--------------------------------------------------------------------------------

shift-unshift : {{_ : Eq X}} (x : X) → (shift x ∙ unshift x) ⊑ later id
shift-unshift x .step x' with x ≟ x
... | no contra with () ← contra refl
... | yes refl = next ⊑-refl

unshift-shift : {{_ : Eq X}} (x : X) → (unshift x ∙ shift x) ⊑ later id
unshift-shift x .step x' with x ≟ x'
... | no _ = ⊥ₗ
... | yes refl = next (lem x)
  where
    lem : (x : X) → (id ∙ shift x) ⊑ (shift x ∙ id)
    lem x .step x' = yield refl (lem x')

⊑-∙-assoc : ∀ {d₁ d₂ d₃}
  → {f : IST X Y d₁} {g : IST Y Z d₂} {h : IST Z W d₃}
  → (f ∙ (g ∙ h)) ⊑ ((f ∙ g) ∙ h)
⊑-∙-assoc {f = f} {g} {h} .step x with f .step x
... | ⊥ = ⊥ₗ
... | next f' = next ⊑-∙-assoc
... | yield y f' with g .step y
...   | ⊥ = ⊥ₗ
...   | next g' = next ⊑-∙-assoc
...   | yield z g' with h .step z
...     | ⊥ = ⊥ₗ
...     | next h' = next ⊑-∙-assoc
...     | yield w h' = yield refl ⊑-∙-assoc

⊑-cong-∙ : ∀ {d₁ d₁' d₂ d₂'}
  → {f : IST X Y d₁} {f' : IST X Y d₁'} {g : IST Y Z d₂} {g' : IST Y Z d₂'}
  → f ⊑ f'
  → g ⊑ g'
  → (f ∙ g) ⊑ (f' ∙ g')
⊑-cong-∙ {f = f} {f'} {g} {g'} f⊑f' g⊑g' .step x
  with f .step x | f' .step x | f⊑f' .step x
... | ⊥ | _ | ⊥ₗ = ⊥ₗ
... | next _ | next _ | next f⊑f' = next (⊑-cong-∙ f⊑f' g⊑g')
... | yield y _ | yield _ _ | yield refl f⊑f' with g .step y | g' .step y | g⊑g' .step y
...   | ⊥ | _ | ⊥ₗ = ⊥ₗ
...   | next _ | next _ | next g⊑g' = next (⊑-cong-∙ f⊑f' g⊑g')
...   | yield _ _ | yield _ _ | yield refl g⊑g' = yield refl (⊑-cong-∙ f⊑f' g⊑g')

⊑-cong-∥ : ∀ {d₁ d₁' d₂ d₂'}
  → {f : IST X Y d₁} {f' : IST X Y d₁'} {g : IST Z W d₂} {g' : IST Z W d₂'}
  → f ⊑ f'
  → g ⊑ g'
  → (f ∥ g) ⊑ (f' ∥ g')
⊑-cong-∥ {f = f} {f'} {g} {g'} f⊑f' g⊑g' .step (x , z)
  with f .step x | f' .step x | g .step z | g' .step z | f⊑f' .step x | g⊑g' .step z
... | ⊥ | _ | _ | _ | ⊥ₗ | _ = ⊥ₗ
... | next _ | next _ | ⊥ | _ | _ | ⊥ₗ = ⊥ₗ
... | yield _ _ | yield _ _ | ⊥ | _ | _ | ⊥ₗ = ⊥ₗ
... | next _ | next _ | next _ | next _ | next f⊑f' | next g⊑g' =
      next (⊑-cong-∥ f⊑f' g⊑g')
... | next f | next f' | yield _ _ | yield _ _ | next {d} {d'} f⊑f' | yield refl _ =
      next (⊑-cong-subst (⊔-identityʳ d) (⊔-identityʳ d') (⊑-cong-∥ f⊑f' (⊑-cong-∙ ⊑-refl g⊑g')))
... | yield _ _ | yield _ _ | next _ | next _ | yield refl _ | next g⊑g' =
      next (⊑-cong-∥ (⊑-cong-∙ (⊑-refl {f = shift x}) f⊑f') g⊑g')
... | yield _ _ | yield _ _ | yield _ _ | yield _ _ | yield refl f⊑f' | yield refl g⊑g' =
      yield refl (⊑-cong-∥ f⊑f' g⊑g')

F-IIST : ∀ (e : E X Y) → (B⟦ e ⟧ ∙ F⟦ e ⟧) ⊑ laterN (DB⟦ e ⟧ + DF⟦ e ⟧) id
F-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → (B⟦ map-fold a f g ⟧ ∙ F⟦ map-fold a f g ⟧) ⊑ id
    helper a .step y with f a .from y in eq
    ... | nothing = ⊥ₗ
    ... | just x rewrite f a .from→to eq = yield refl (helper (g a x))
F-IIST (delay x) = unshift-shift x
F-IIST (hasten x) = shift-unshift x
F-IIST (e ⟫ e') =
  let ih = F-IIST e
      ih' = F-IIST e'
      foo : ((B⟦ e ⟧ ∙ F⟦ e ⟧) ∙ F⟦ e' ⟧) ⊑ _
      foo = ⊑-cong-∙ ih ⊑-refl
      bar : (B⟦ e ⟧ ∙ (F⟦ e ⟧ ∙ F⟦ e' ⟧)) ⊑ _
      bar = ⊑-trans ⊑-∙-assoc foo
      baz : (B⟦ e' ⟧ ∙ (B⟦ e ⟧ ∙ (F⟦ e ⟧ ∙ F⟦ e' ⟧))) ⊑ _
      baz = ⊑-cong-∙ ⊑-refl bar
   in {!   !}
F-IIST (e ⊗ e') =
  let ih = F-IIST e
      ih' = F-IIST e'
   in {!   !}

B-IIST : ∀ (e : E X Y) → (F⟦ e ⟧ ∙ B⟦ e ⟧) ⊑ laterN (DF⟦ e ⟧ + DB⟦ e ⟧) id
B-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → (F⟦ map-fold a f g ⟧ ∙ B⟦ map-fold a f g ⟧) ⊑ id
    helper a .step x with f a .to x in eq
    ... | nothing = ⊥ₗ
    ... | just y rewrite f a .to→from eq = yield refl (helper (g a x))
B-IIST (delay x) = shift-unshift x
B-IIST (hasten x) = unshift-shift x
B-IIST (e ⟫ e') =
  let ih = B-IIST e
      ih' = B-IIST e'
   in {!   !}
B-IIST (e ⊗ e') =
  let ih = B-IIST e
      ih' = B-IIST e'
   in {!   !}
