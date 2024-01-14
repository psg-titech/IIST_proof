{-# OPTIONS --guardedness #-}

module IIST.StateMachine where

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

infixl 9 _∙_
infixl 8 _∥_

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
F⟦ e ⋙ e' ⟧ = F⟦ e ⟧ ∙ F⟦ e' ⟧
F⟦ e ⊗ e' ⟧ = F⟦ e ⟧ ∥ F⟦ e' ⟧

B⟦_⟧ : (e : E X Y) → IST Y X DB⟦ e ⟧
B⟦ map-fold a f g ⟧ = B-map-fold a f g
B⟦ delay x ⟧ = unshift x
B⟦ hasten x ⟧ = shift x
B⟦ e ⋙ e' ⟧ = B⟦ e' ⟧ ∙ B⟦ e ⟧
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

infix 4 _≈_ _Step≈_

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
  → f ≈ h
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
-- More defined: like _≈_ but the LHS may ⊥ earlier

infix 4 _⊑_ _Step⊑_

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

∙-identityₗ : ∀ {d} {f : IST X Y d} → id ∙ f ≈ f
∙-identityₗ {f = f} .step x with f .step x
... | ⊥ = ⊥
... | next f' = next ∙-identityₗ
... | yield y f' = yield refl ∙-identityₗ

∙-identityᵣ : ∀ {d} {f : IST X Y d} → f ∙ id ≈ f
∙-identityᵣ {f = f} .step x with f .step x
... | ⊥ = ⊥
... | next f' = next ∙-identityᵣ
... | yield y f' = yield refl ∙-identityᵣ

∙-assoc : ∀ {d₁ d₂ d₃}
  → {f : IST X Y d₁} {g : IST Y Z d₂} {h : IST Z W d₃}
  → f ∙ (g ∙ h) ≈ (f ∙ g) ∙ h
∙-assoc {f = f} {g} {h} .step x with f .step x
... | ⊥ = ⊥
... | next f' = next ∙-assoc
... | yield y f' with g .step y
...   | ⊥ = ⊥
...   | next g' = next ∙-assoc
...   | yield z g' with h .step z
...     | ⊥ = ⊥
...     | next h' = next ∙-assoc
...     | yield w h' = yield refl ∙-assoc

≈-cong-∙ : ∀ {d₁ d₁' d₂ d₂'}
  → {f : IST X Y d₁} {f' : IST X Y d₁'} {g : IST Y Z d₂} {g' : IST Y Z d₂'}
  → f ≈ f'
  → g ≈ g'
  → f ∙ g ≈ f' ∙ g'
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
  → f ∥ g ≈ f' ∥ g'
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
      next (≈-cong-∥ (≈-cong-∙ ≈-refl f≈f') g≈g')
... | yield _ _ | yield _ _ | yield _ _ | yield _ _ | yield refl f≈f' | yield refl g≈g' =
      yield refl (≈-cong-∥ f≈f' g≈g')

≈-cong-later : ∀ {d d'} {f : IST X Y d} {g : IST X Y d'}
  → f ≈ g
  → later f ≈ later g
≈-cong-later {f = f} {g} f≈g .step x with f .step x | g .step x | f≈g .step x
... | ⊥ | ⊥ | ⊥ = next (≈-cong-∙ ≈-refl f≈g)
... | next _ | next _ | next _ = next (≈-cong-∙ ≈-refl f≈g)
... | yield _ _ | yield _ _ | yield _ _ = next (≈-cong-∙ ≈-refl f≈g)

≈-cong-laterN : ∀ {n d d'} {f : IST X Y d} {g : IST X Y d'}
  → f ≈ g
  → laterN n f ≈ laterN n g
≈-cong-laterN {n = zero} f≈g = f≈g
≈-cong-laterN {n = suc n} f≈g = ≈-cong-later (≈-cong-laterN {n = n} f≈g)

∙-later : ∀ {d d'} {f : IST X Y d} {g : IST Y Z d'}
  → later f ∙ g ≈ later (f ∙ g)
∙-later .step x = next (≈-sym ∙-assoc)

∙-laterN : ∀ {n d d'} {f : IST X Y d} {g : IST Y Z d'}
  → laterN n f ∙ g ≈ laterN n (f ∙ g)
∙-laterN {n = zero} = ≈-refl
∙-laterN {n = suc n} = ≈-trans ∙-later (≈-cong-later (∙-laterN {n = n}))

laterN-join : ∀ {d m n} {f : IST X Y d}
  → laterN m (laterN n f) ≈ laterN (m + n) f
laterN-join {m = zero} = ≈-refl
laterN-join {m = suc m} = ≈-cong-later (laterN-join {m = m})

laterN-subst : ∀ {m n d} {f : IST X Y d}
  → m ≡ n
  → laterN m f ≈ laterN n f
laterN-subst refl = ≈-refl

F∘I≈B : ∀ (e : E X Y) → F⟦ I⟦ e ⟧ ⟧ ≈ B⟦ e ⟧
F∘I≈B (map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → F⟦ I⟦ map-fold a f g ⟧ ⟧ ≈ B⟦ map-fold a' f g ⟧
    helper {a} refl .step y with f a .from y in eq
    ... | nothing = ⊥
    ... | just x = yield refl (helper (cong (Maybe.maybe (g a) a) eq))
F∘I≈B (delay x) = ≈-refl
F∘I≈B (hasten x) = ≈-refl
F∘I≈B (e ⋙ e') = ≈-cong-∙ (F∘I≈B e') (F∘I≈B e)
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
B∘I≈F (e ⋙ e') = ≈-cong-∙ (B∘I≈F e) (B∘I≈F e')
B∘I≈F (e ⊗ e') = ≈-cong-∥ (B∘I≈F e) (B∘I≈F e')

--------------------------------------------------------------------------------

shift-unshift : {{_ : Eq X}} (x : X) → shift x ∙ unshift x ⊑ later id
shift-unshift x .step x' with x ≟ x
... | no contra with () ← contra refl
... | yes refl = next ⊑-refl

unshift-shift : {{_ : Eq X}} (x : X) → unshift x ∙ shift x ⊑ later id
unshift-shift x .step x' with x ≟ x'
... | no _ = ⊥ₗ
... | yes refl = next (lem x)
  where
    lem : (x : X) → (id ∙ shift x) ⊑ (shift x ∙ id)
    lem x .step x' = yield refl (lem x')

⊑-cong-∙ : ∀ {d₁ d₁' d₂ d₂'}
  → {f : IST X Y d₁} {f' : IST X Y d₁'} {g : IST Y Z d₂} {g' : IST Y Z d₂'}
  → f ⊑ f'
  → g ⊑ g'
  → f ∙ g ⊑ f' ∙ g'
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
  → f ∥ g ⊑ f' ∥ g'
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
      next (⊑-cong-∥ (⊑-cong-∙ ⊑-refl f⊑f') g⊑g')
... | yield _ _ | yield _ _ | yield _ _ | yield _ _ | yield refl f⊑f' | yield refl g⊑g' =
      yield refl (⊑-cong-∥ f⊑f' g⊑g')

⊑-cong-later : ∀ {d d'} {f : IST X Y d} {g : IST X Y d'}
  → f ⊑ g
  → later f ⊑ later g
⊑-cong-later {f = f} {g} f⊑g .step x with f .step x | g .step x | f⊑g .step x
... | ⊥ | _ | ⊥ₗ = next (⊑-cong-∙ ⊑-refl f⊑g)
... | next _ | next _ | next _ = next (⊑-cong-∙ ⊑-refl f⊑g)
... | yield _ _ | yield _ _ | yield _ _ = next (⊑-cong-∙ ⊑-refl f⊑g)

⊑-cong-laterN : ∀ {n d d'} {f : IST X Y d} {g : IST X Y d'}
  → f ⊑ g
  → laterN n f ⊑ laterN n g
⊑-cong-laterN {n = zero} f⊑g = f⊑g
⊑-cong-laterN {n = suc n} f⊑g = ⊑-cong-later (⊑-cong-laterN {n = n} f⊑g)

later-shift-yield : ∀ {d} {f f' : IST X Y 0} {g : IST Y Z d} {x : X} {y : Y}
  → f .step x ≡ yield y f'
  → f' ∙ (shift y ∙ g) ⊑ shift x ∙ (f ∙ g)
later-shift-yield {f' = f'} {g} {y = y} p .step x' rewrite p
  with f' .step x' in eq | g .step y in eq'
... | ⊥ | _ = ⊥ₗ
... | yield y' f'' | ⊥ rewrite eq' = ⊥ₗ
... | yield y' f'' | next g' rewrite eq' = next (later-shift-yield eq)
... | yield y' f'' | yield z g' rewrite eq' = yield refl (later-shift-yield eq)

later-shift-next : ∀ {d d'}
  → {f : IST X Y (suc d)} {f' : IST X Y d} {g : IST Y Z d'} {x : X}
  → f .step x ≡ next f'
  → f' ∙ later g ⊑ shift x ∙ (f ∙ g)
later-shift-next {f' = f'} p .step x' rewrite p with f' .step x' in eq
... | ⊥ = ⊥ₗ
... | next f'' = next (later-shift-next eq)
... | yield y f'' = next (later-shift-yield eq)

⊑-∙-later : ∀ {d d'} {f : IST X Y d} {g : IST Y Z d'}
  → f ∙ later g ⊑ later (f ∙ g)
⊑-∙-later {f = f} {g} .step x with f .step x in eq
... | ⊥ = ⊥ₗ
... | next f' = next (later-shift-next eq)
... | yield y f' = next (later-shift-yield eq)

⊑-∙-laterN : ∀ {n d d'} {f : IST X Y d} {g : IST Y Z d'}
  → f ∙ laterN n g ⊑ laterN n (f ∙ g)
⊑-∙-laterN {n = zero} = ⊑-refl
⊑-∙-laterN {n = suc n} = ⊑-trans ⊑-∙-later (⊑-cong-later (⊑-∙-laterN {n = n}))

add-shuffle : ∀ m n o p → (m + n) + (o + p) ≡ (o + m) + (n + p)
add-shuffle = solve-∀
  where open import Data.Nat.Tactic.RingSolver

∙-IIST : ∀ {d₁ d₁' d₂ d₂'}
  → {f : IST X Y d₁} {f' : IST Y X d₁'} {g : IST Y Z d₂} {g' : IST Z Y d₂'}
  → f ∙ f' ⊑ laterN (d₁ + d₁') id
  → g ∙ g' ⊑ laterN (d₂ + d₂') id
  → (f ∙ g) ∙ (g' ∙ f') ⊑ laterN ((d₁ + d₂) + (d₂' + d₁')) id
∙-IIST {d₁ = d₁} {d₁'} {d₂} {d₂'} {f} {f'} {g} {g'} p q = h10
  where
    h1 : (g ∙ g') ∙ f' ⊑ laterN (d₂ + d₂') id ∙ f'
    h2 : (g ∙ g') ∙ f' ⊑ laterN (d₂ + d₂') (id ∙ f')
    h3 : (g ∙ g') ∙ f' ⊑ laterN (d₂ + d₂') f'
    h4 : g ∙ (g' ∙ f') ⊑ laterN (d₂ + d₂') f'
    h5 : f ∙ (g ∙ (g' ∙ f')) ⊑ f ∙ laterN (d₂ + d₂') f'
    h6 : (f ∙ g) ∙ (g' ∙ f') ⊑ f ∙ laterN (d₂ + d₂') f'
    h7 : (f ∙ g) ∙ (g' ∙ f') ⊑ laterN (d₂ + d₂') (f ∙ f')
    h8 : (f ∙ g) ∙ (g' ∙ f') ⊑ laterN (d₂ + d₂') (laterN (d₁ + d₁') id)
    h9 : (f ∙ g) ∙ (g' ∙ f') ⊑ laterN ((d₂ + d₂') + (d₁ + d₁')) id
    h10 : (f ∙ g) ∙ (g' ∙ f') ⊑ laterN ((d₁ + d₂) + (d₂' + d₁')) id
    h1 = ⊑-cong-∙ q ⊑-refl
    h2 = ⊑-trans h1 (≈-to-⊑ (∙-laterN {n = d₂ + d₂'}))
    h3 = ⊑-trans h2 (≈-to-⊑ (≈-cong-laterN {n = d₂ + d₂'} ∙-identityₗ))
    h4 = ⊑-trans (≈-to-⊑ ∙-assoc) h3
    h5 = ⊑-cong-∙ ⊑-refl h4
    h6 = ⊑-trans (≈-to-⊑ (≈-sym ∙-assoc)) h5
    h7 = ⊑-trans h6 (⊑-∙-laterN {n = d₂ + d₂'})
    h8 = ⊑-trans h7 (⊑-cong-laterN {n = d₂ + d₂'} p)
    h9 = ⊑-trans h8 (≈-to-⊑ (laterN-join {m = d₂ + d₂'} {n = d₁ + d₁'}))
    h10 = ⊑-trans h9 (≈-to-⊑ (laterN-subst (add-shuffle d₂ d₂' d₁ d₁')))

∥-IIST : ∀ {d₁ d₁' d₂ d₂'}
  → {f : IST X Y d₁} {f' : IST Y X d₁'} {g : IST Z W d₂} {g' : IST W Z d₂'}
  → f ∙ f' ⊑ laterN (d₁ + d₁') id
  → g ∙ g' ⊑ laterN (d₂ + d₂') id
  → (f ∥ g) ∙ (f' ∥ g') ⊑ laterN ((d₁ ⊔ d₂) + (d₁' ⊔ d₂')) id
∥-IIST {d₁ = d₁} {d₁'} {d₂} {d₂'} {f} {f'} {g} {g'} p q = {!   !}

F-IIST : ∀ (e : E X Y) → B⟦ e ⟧ ∙ F⟦ e ⟧ ⊑ laterN (DB⟦ e ⟧ + DF⟦ e ⟧) id
F-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → (B⟦ map-fold a f g ⟧ ∙ F⟦ map-fold a f g ⟧) ⊑ id
    helper a .step y with f a .from y in eq
    ... | nothing = ⊥ₗ
    ... | just x rewrite f a .from→to eq = yield refl (helper (g a x))
F-IIST (delay x) = unshift-shift x
F-IIST (hasten x) = shift-unshift x
F-IIST (e ⋙ e') = ∙-IIST (F-IIST e') (F-IIST e)
F-IIST (e ⊗ e') = ∥-IIST (F-IIST e) (F-IIST e')

B-IIST : ∀ (e : E X Y) → F⟦ e ⟧ ∙ B⟦ e ⟧ ⊑ laterN (DF⟦ e ⟧ + DB⟦ e ⟧) id
B-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → (F⟦ map-fold a f g ⟧ ∙ B⟦ map-fold a f g ⟧) ⊑ id
    helper a .step x with f a .to x in eq
    ... | nothing = ⊥ₗ
    ... | just y rewrite f a .to→from eq = yield refl (helper (g a x))
B-IIST (delay x) = shift-unshift x
B-IIST (hasten x) = unshift-shift x
B-IIST (e ⋙ e') = ∙-IIST (B-IIST e) (B-IIST e')
B-IIST (e ⊗ e') = ∥-IIST (B-IIST e) (B-IIST e')
