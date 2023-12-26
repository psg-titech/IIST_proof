{-# OPTIONS --guardedness --sized-types #-}

module IIST.Experiment where

open import Size
open import Codata.Sized.Thunk using ( Thunk; force )
open import Data.Maybe.Base as Maybe using ( Maybe; just; nothing )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Nat.Instances
open import Data.Nat.Properties using ( +-suc; +-identityʳ; ⊔-identityʳ )
open import Data.List.Base using ( List; []; _∷_ )
open import Data.Product.Base using ( _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; subst )
open import Relation.Binary.TypeClasses using ( _≟_ )
open import Relation.Nullary using ( ¬_; yes; no )

open import IIST.Common

private
  variable
    i : Size
    A X Y Z W : Set

mutual

  ⟨_⟩-IST : ℕ → Set → Set → Size → Set
  ⟨ d ⟩-IST X Y i = X → Step X Y i d

  data Step (X Y : Set) (i : Size) : ℕ → Set where
    fail : ∀ {d} → Step X Y i d
    next : ∀ {d} → Thunk (⟨ d ⟩-IST X Y) i → Step X Y i (suc d)
    yield : Y → Thunk (⟨ 0 ⟩-IST X Y) i → Step X Y i 0

feed : ∀ {d} → ⟨ d ⟩-IST X Y ∞ → List X → Maybe (List Y)
feed f [] = just []
feed f (x ∷ xs) with f x
... | fail = nothing
... | next f' = feed (force f') xs
... | yield y f' = Maybe.map (y ∷_) (feed (force f') xs)

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ⟨ 0 ⟩-IST X Y i
F-map-fold a f g x with f a .to x
... | nothing = fail
... | just y = yield y λ where .force → F-map-fold (g a x) f g

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ⟨ 0 ⟩-IST Y X i
B-map-fold a f g y with f a .from y
... | nothing = fail
... | just x = yield x λ where .force → B-map-fold (g a x) f g

id : ⟨ 0 ⟩-IST X X i
id x = yield x λ where .force → id

shift : X → ⟨ 0 ⟩-IST X X i
shift x y = yield x λ where .force → shift y

unshift : {{_ : Eq X}} → X → ⟨ 1 ⟩-IST X X i
unshift x y with x ≟ y
... | no _ = fail
... | yes refl = next λ where .force → id

_∙_ : ∀ {d d'} → ⟨ d ⟩-IST X Y i → ⟨ d' ⟩-IST Y Z i → ⟨ d + d' ⟩-IST X Z i
(f ∙ g) x with f x
... | fail = fail
... | next f' = next λ where .force → force f' ∙ g
... | yield y f' with g y
...   | fail = fail
...   | next g' = next λ where .force → force f' ∙ force g'
...   | yield z g' = yield z λ where .force → force f' ∙ force g'

delay : ∀ {d} → ⟨ d ⟩-IST X Y i → ⟨ suc d ⟩-IST X Y i
delay f x = next λ where .force → shift x ∙ f

_∥_ : ∀ {d d'} → ⟨ d ⟩-IST X Y i → ⟨ d' ⟩-IST Z W i → ⟨ d ⊔ d' ⟩-IST (X × Z) (Y × W) i
_∥_ {d = zero} {zero} f g (x , z) with f x | g z
... | fail       | fail       = fail
... | fail       | yield _ _  = fail
... | yield _ _  | fail       = fail
... | yield y f' | yield w g' = yield (y , w) λ where .force → force f' ∥ force g'
_∥_ {d = zero} {suc d'} f g (x , z) with g z
... | fail = fail
... | next g' = next λ where .force → (shift x ∙ f) ∥ force g'
_∥_ {d = suc d} {zero} f g (x , z) with f x
... | fail = fail
... | next f' = next λ where
        .force {j} → subst (λ d → ⟨ d ⟩-IST _ _ j) (⊔-identityʳ d) (force f' ∥ (shift z ∙ g))
_∥_ {d = suc d} {suc d'} f g (x , z) with f x | g z
... | fail    | fail    = fail
... | fail    | next _  = fail
... | next _  | fail    = fail
... | next f' | next g' = next λ where .force → force f' ∥ force g'

--------------------------------------------------------------------------------
-- Bisimulation

mutual

  _⊢_≈_ : Size → {d : ℕ} (f g : ⟨ d ⟩-IST X Y ∞) → Set
  i ⊢ f ≈ g = ∀ x → i ⊢ f x Step≈ g x

  data _⊢_Step≈_ (i : Size) {X Y : Set} : ∀ {d} (s s' : Step X Y ∞ d) → Set where
    fail : ∀ {d} → i ⊢ (fail {d = d}) Step≈ fail
    next : ∀ {d} {f g : Thunk (⟨ d ⟩-IST X Y) ∞}
      → Thunk (_⊢ force f ≈ force g) i
      → i ⊢ next f Step≈ next g
    yield : ∀ {x y f g}
      → x ≡ y
      → Thunk (_⊢ force f ≈ force g) i
      → i ⊢ yield x f Step≈ yield y g

≈-refl : ∀ {d} {f : ⟨ d ⟩-IST X Y ∞} → i ⊢ f ≈ f
≈-refl {f = f} x with f x
... | fail = fail
... | next f' = next λ where .force → ≈-refl
... | yield y f' = yield refl λ where .force → ≈-refl

≈-sym : ∀ {d} {f g : ⟨ d ⟩-IST X Y ∞} → i ⊢ f ≈ g → i ⊢ g ≈ f
≈-sym {d = zero} {f} {g} f≈g x with f x | g x | f≈g x
... | fail | fail | fail = fail
... | yield _ _ | yield _ _ | yield refl f'≈g' =
      yield refl λ where .force → ≈-sym (force f'≈g')
≈-sym {d = suc d} {f} {g} f≈g x with f x | g x | f≈g x
... | fail | fail | fail = fail
... | next _ | next _ | next f'≈g' =
      next λ where .force → ≈-sym (force f'≈g')

≈-trans : ∀ {d} {f g h : ⟨ d ⟩-IST X Y ∞} → i ⊢ f ≈ g → i ⊢ g ≈ h → i ⊢ f ≈ h
≈-trans {d = zero} {f} {g} {h} f≈g g≈h x with f x | g x | h x | f≈g x | g≈h x
... | fail | fail | fail | fail | fail = fail
... | yield _ _ | yield _ _ | yield _ _ | yield refl f'≈g' | yield refl g'≈h' =
      yield refl λ where .force → ≈-trans (force f'≈g') (force g'≈h')
≈-trans {d = suc d} {f} {g} {h} f≈g g≈h x with f x | g x | h x | f≈g x | g≈h x
... | fail | fail | fail | fail | fail = fail
... | next _ | next _ | next _ | next f'≈g' | next g'≈h' =
      next λ where .force → ≈-trans (force f'≈g') (force g'≈h')

≈-feed : ∀ {d} {f g : ⟨ d ⟩-IST X Y ∞}
  → ∞ ⊢ f ≈ g
  → ∀ xs → feed f xs ≡ feed g xs
≈-feed f≈g [] = refl
≈-feed {f = f} {g} f≈g (x ∷ xs) with f x | g x | f≈g x
... | fail | fail | fail = refl
... | next _ | next _ | next f'≈g' rewrite ≈-feed (force f'≈g') xs = refl
... | yield _ _ | yield _ _ | yield refl f'≈g' rewrite ≈-feed (force f'≈g') xs = refl

--------------------------------------------------------------------------------

map-fold-lem1 : ∀ a (f : A → X ⇌ Y) g
  → i ⊢ (F-map-fold a f g ∙ B-map-fold a f g) ≈ id
map-fold-lem1 a f g x with f a .to x in eq
... | nothing = {!   !}
... | just y rewrite f a .invertible₁ eq =
      yield refl λ where .force → map-fold-lem1 (g a x) f g

map-fold-lem2 : ∀ a (f : A → X ⇌ Y) g
  → i ⊢ (B-map-fold a f g ∙ F-map-fold a f g) ≈ id
map-fold-lem2 a f g y with f a .from y in eq
... | nothing = {!   !}
... | just x rewrite f a .invertible₂ eq =
      yield refl λ where .force → map-fold-lem2 (g a x) f g

shift-unshift : {{_ : Eq X}} (x : X) → i ⊢ (shift x ∙ unshift x) ≈ delay id
shift-unshift x x' with x ≟ x
... | no contra with () ← contra refl
... | yes refl = next λ where .force → ≈-refl

unshift-shift : {{_ : Eq X}} (x : X) → i ⊢ (unshift x ∙ shift x) ≈ delay id
unshift-shift x x' with x ≟ x'
... | no _ = {!   !}
... | yes refl = next λ where .force → lem x
  where
    lem : (x : X) → i ⊢ (id ∙ shift x) ≈ (shift x ∙ id)
    lem x x' = yield refl λ where .force → lem x'

--------------------------------------------------------------------------------
-- Examples

_ : feed (shift 10) (0 ∷ 1 ∷ 2 ∷ []) ≡ just (10 ∷ 0 ∷ 1 ∷ [])
_ = refl

_ : feed (unshift 0) (0 ∷ 1 ∷ 2 ∷ []) ≡ just (1 ∷ 2 ∷ [])
_ = refl

_ : feed (unshift 10) (0 ∷ 1 ∷ 2 ∷ []) ≡ nothing
_ = refl

_ : feed (delay id) (0 ∷ 1 ∷ 2 ∷ []) ≡ just (0 ∷ 1 ∷ [])
_ = refl

_ : feed (delay id ∙ shift 10) (0 ∷ 1 ∷ 2 ∷ []) ≡ just (10 ∷ 0 ∷ [])
_ = refl

_ : feed (shift 100 ∥ unshift 0) ((0 , 0) ∷ (1 , 1) ∷ (2 , 2) ∷ (3 , 3) ∷ (4 , 4) ∷ [])
  ≡ just ((100 , 1) ∷ (0 , 2) ∷ (1 , 3) ∷ (2 , 4) ∷ [])
_ = refl
