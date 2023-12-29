{-# OPTIONS --guardedness #-}

module IIST.Experiment.DefinitionallyIncremental where

open import Data.Maybe.Base as Maybe using ( Maybe; just; nothing )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_; NonZero )
open import Data.Nat.Properties using ( +-suc; +-identityʳ; ⊔-identityʳ; +-comm )
open import Data.List.Base using ( List; []; _∷_ )
open import Data.Product.Base using ( _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; cong; subst )
open import Relation.Nullary using ( yes; no )

open import IIST.Common
open import IIST.Syntax

private
  variable
    A X Y Z W : Set

--------------------------------------------------------------------------------
-- Definitionally d-IST

mutual

  IST : ℕ → Set → Set → Set
  IST d X Y = X → Step d X Y

  data Step (d : ℕ) (X Y : Set) : Set where
    fail : Step d X Y
    next : ∀ {d'} → d ≡ suc d' → ∞IST d' X Y → Step d X Y
    yield : d ≡ 0 → Y → ∞IST 0 X Y → Step d X Y

  record ∞IST (d : ℕ) (X Y : Set) : Set where
    coinductive
    field force : IST d X Y

open ∞IST

pattern next! f = next refl f
pattern yield! y f = yield refl y f

feed : ∀ {d} → IST d X Y → List X → Maybe (List Y)
feed f [] = just []
feed f (x ∷ xs) with f x
... | fail = nothing
... | next! f' = feed (force f') xs
... | yield! y f' = Maybe.map (y ∷_) (feed (force f') xs)

--------------------------------------------------------------------------------
-- Semantics

id : IST 0 X X
id x = yield! x λ where .force → id

shift : X → IST 0 X X
shift x y = yield! x λ where .force → shift y

unshift : {{_ : Eq X}} → X → IST 1 X X
unshift x y with x ≟ y
... | no _ = fail
... | yes refl = next! λ where .force → id

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → IST 0 X Y
F-map-fold a f g x with f a .to x
... | nothing = fail
... | just y = yield! y λ where .force → F-map-fold (g a x) f g

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → IST 0 Y X
B-map-fold a f g y with f a .from y
... | nothing = fail
... | just x = yield! x λ where .force → B-map-fold (g a x) f g

_∙_ : ∀ {d d'} → IST d X Y → IST d' Y Z → IST (d + d') X Z
(f ∙ g) x with f x
... | fail = fail
... | next! f' = next! λ where .force → force f' ∙ g
... | yield! y f' with g y
...   | fail = fail
...   | next! g' = next! λ where .force → force f' ∙ force g'
...   | yield! z g' = yield! z λ where .force → force f' ∙ force g'

later : ∀ {d} → IST d X Y → IST (suc d) X Y
later f x = next! λ where .force → shift x ∙ f

_∥_ : ∀ {d d'} → IST d X Y → IST d' Z W → IST (d ⊔ d') (X × Z) (Y × W)
(f ∥ g) (x , z) with f x | g z
... | fail        | _           = fail
... | _           | fail        = fail
... | next! f'    | next! g'    = next! λ where .force → force f' ∥ force g'
... | next! f'    | yield! _ _  = next (cong suc (sym (⊔-identityʳ _))) λ where .force → force f' ∥ (shift z ∙ g)
... | yield! _ _  | next! g'    = next! λ where .force → (shift x ∙ f) ∥ force g'
... | yield! y f' | yield! w g' = yield! (y , w) λ where .force → force f' ∥ force g'

F⟦_⟧ : (e : E X Y) → IST (DF⟦ e ⟧) X Y
F⟦ map-fold a f g ⟧ = F-map-fold a f g
F⟦ delay x ⟧ = shift x
F⟦ hasten x ⟧ = unshift x
F⟦ e ⟫ e' ⟧ = F⟦ e ⟧ ∙ F⟦ e' ⟧
F⟦ e ⊗ e' ⟧ = F⟦ e ⟧ ∥ F⟦ e' ⟧

B⟦_⟧ : (e : E X Y) → IST (DB⟦ e ⟧) Y X
B⟦ map-fold a f g ⟧ = B-map-fold a f g
B⟦ delay x ⟧ = unshift x
B⟦ hasten x ⟧ = shift x
B⟦ e ⟫ e' ⟧ = B⟦ e' ⟧ ∙ B⟦ e ⟧
B⟦ e ⊗ e' ⟧ = B⟦ e ⟧ ∥ B⟦ e' ⟧

--------------------------------------------------------------------------------
-- Bisimulation

mutual

  _≈_ : ∀ {d d'} → IST d X Y → IST d' X Y → Set
  f ≈ g = ∀ x → f x Step≈ g x

  data _Step≈_ {X Y d} :  Step d X Y → ∀ {d'} → Step d' X Y → Set where
    ≈fail : fail Step≈ fail {d = d}
    ≈next : ∀ {d'} {f : ∞IST d' X Y} {g : ∞IST d' X Y}
      → (p : d ≡ suc d')
      → f ∞≈ g
      → next p f Step≈ next p g
    ≈yield : ∀ {x y f g}
      → (p : d ≡ 0)
      → x ≡ y
      → f ∞≈ g
      → yield p x f Step≈ yield p y g

  record _∞≈_ {d d'} (f : ∞IST d X Y) (g : ∞IST d' X Y): Set where
    coinductive
    field force : force f ≈ force g

open _∞≈_

pattern ≈next! f≈g = ≈next refl f≈g
pattern ≈yield! x≡y f≈g = ≈yield refl x≡y f≈g

≈-refl : ∀ {d} {f : IST d X Y} → f ≈ f
≈-refl {f = f} x with f x
... | fail = ≈fail
... | next! f' = ≈next! λ where .force → ≈-refl
... | yield! y f' = ≈yield! refl λ where .force → ≈-refl

≈-sym : ∀ {d} {f g : IST d X Y} → f ≈ g → g ≈ f
≈-sym {f = f} {g = g} f≈g x with f x | g x | f≈g x
... | fail | fail | ≈fail = ≈fail
... | next! _ | next! _ | ≈next! f'≈g' =
      ≈next! λ where .force → ≈-sym (force f'≈g')
... | yield! _ _ | yield! _ _ | ≈yield! refl f'≈g' =
      ≈yield! refl λ where .force → ≈-sym (force f'≈g')

≈-trans : ∀ {d} {f g h : IST d X Y} → f ≈ g → g ≈ h → f ≈ h
≈-trans {f = f} {g = g} {h = h} f≈g g≈h x with f x | g x | h x | f≈g x | g≈h x
... | fail | fail | fail | ≈fail | ≈fail = ≈fail
... | next! _ | next! _ | next! _ | ≈next! f'≈g' | ≈next! g'≈h' =
      ≈next! λ where .force → ≈-trans (force f'≈g') (force g'≈h')
... | yield! _ _ | yield! _ _ | yield! _ _ | ≈yield! refl f'≈g' | ≈yield! refl g'≈h' =
      ≈yield! refl λ where .force → ≈-trans (force f'≈g') (force g'≈h')

≈-feed : ∀ {d} {f g : IST d X Y}
  → f ≈ g
  → ∀ xs → feed f xs ≡ feed g xs
≈-feed f≈g [] = refl
≈-feed {f = f} {g} f≈g (x ∷ xs) with f x | g x | f≈g x
... | fail | fail | ≈fail! = refl
... | next! _ | next! _ | ≈next! f'≈g'
      rewrite ≈-feed (force f'≈g') xs = refl
... | yield! _ _ | yield! _ _ | ≈yield! refl f'≈g'
      rewrite ≈-feed (force f'≈g') xs = refl

-- --------------------------------------------------------------------------------

∙-≈ : ∀ {d d'} {f f' : IST d X Y} {g g' : IST d' Y Z}
  → f ≈ f'
  → g ≈ g'
  → (f ∙ g) ≈ (f' ∙ g')
∙-≈ {f = f} {f'} {g} {g'} f≈f' g≈g' x with f x | f' x | f≈f' x
... | fail | fail | ≈fail = ≈fail
... | next! _ | next! _ | ≈next! f≈f' = ≈next! λ where .force → ∙-≈ (force f≈f') g≈g'
... | yield! y _ | yield! _ _ | ≈yield! refl f≈f' with g y | g' y | g≈g' y
...   | fail | fail | ≈fail = ≈fail
...   | next! _ | next! _ | ≈next! g≈g' = ≈next! λ where .force → ∙-≈ (force f≈f') (force g≈g')
...   | yield! _ _ | yield! _ _ | ≈yield! refl g≈g' = ≈yield! refl λ where .force → ∙-≈ (force f≈f') (force g≈g')

∥-≈ : ∀ {d d'} {f f' : IST d X Y} {g g' : IST d' Z W}
  → f ≈ f'
  → g ≈ g'
  → (f ∥ g) ≈ (f' ∥ g')
∥-≈ {f = f} {f'} {g} {g'} f≈f' g≈g' (x , z) with f x | f' x | g z | g' z | f≈f' x | g≈g' z
... | fail | fail | fail | fail | ≈fail | ≈fail = ≈fail
... | fail | fail | next! _ | next! _ | ≈fail | ≈next! _ = ≈fail
... | fail | fail | yield! _ _ | yield! _ _ | ≈fail | ≈yield! _ _ = ≈fail
... | next! _ | next! _ | fail | fail | ≈next! _ | ≈fail = ≈fail
... | next! _ | next! _ | next! _ | next! _ | ≈next! f≈f' | ≈next! g≈g' =
      ≈next! λ where .force → ∥-≈ (force f≈f') (force g≈g')
... | next! _ | next! _ | yield! _ _ | yield! _ _ | ≈next! f≈f' | ≈yield! refl _ =
      ≈next (cong suc (sym (⊔-identityʳ _))) λ where .force → ∥-≈ (force f≈f') (∙-≈ ≈-refl g≈g')
... | yield! _ _ | yield! _ _ | fail | fail | ≈yield! refl f≈f' | ≈fail = ≈fail
... | yield! _ _ | yield! _ _ | next! _ | next! _ | ≈yield! refl _ | ≈next! g≈g' =
      ≈next! λ where .force → ∥-≈ (∙-≈ ≈-refl f≈f') (force g≈g')
... | yield! _ _ | yield! _ _ | yield _ _ _ | yield _ _ _ | ≈yield! refl f≈f' | ≈yield! refl g≈g' =
      ≈yield! refl λ where .force → ∥-≈ (force f≈f') (force g≈g')

F∘I≈B : ∀ (e : E X Y) → F⟦ I⟦ e ⟧ ⟧ ≈ B⟦ e ⟧
F∘I≈B (map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → F⟦ I⟦ map-fold a f g ⟧ ⟧ ≈ B⟦ map-fold a' f g ⟧
    helper {a} refl y with f a .from y in eq
    ... | nothing = ≈fail
    ... | just x = ≈yield! refl λ where .force → helper (cong (Maybe.maybe (g a) a) eq)
F∘I≈B (delay x) = ≈-refl
F∘I≈B (hasten x) = ≈-refl
F∘I≈B (e ⟫ e') = {!   !} -- ∙-≈ (F∘I≈B e') (F∘I≈B e)
F∘I≈B (e ⊗ e') = {!   !}

--------------------------------------------------------------------------------

-- map-fold-lem1 : ∀ a (f : A → X ⇌ Y) g
--   → (F-map-fold a f g ∙ B-map-fold a f g) ≈ id
-- map-fold-lem1 a f g x with f a .to x in eq
-- ... | nothing = {!   !}
-- ... | just y rewrite f a .to→from eq =
--       yield refl λ where .force → map-fold-lem1 (g a x) f g

-- map-fold-lem2 : ∀ a (f : A → X ⇌ Y) g
--   → (B-map-fold a f g ∙ F-map-fold a f g) ≈ id
-- map-fold-lem2 a f g y with f a .from y in eq
-- ... | nothing = {!   !}
-- ... | just x rewrite f a .from→to eq =
--       yield refl λ where .force → map-fold-lem2 (g a x) f g

-- shift-unshift : {{_ : Eq X}} (x : X) → (shift x ∙ unshift x) ≈ later id
-- shift-unshift x x' with x ≟ x
-- ... | no contra with () ← contra refl
-- ... | yes refl = next λ where .force → ≈-refl

-- unshift-shift : {{_ : Eq X}} (x : X) → (unshift x ∙ shift x) ≈ later id
-- unshift-shift x x' with x ≟ x'
-- ... | no _ = {!   !}
-- ... | yes refl = next λ where .force → lem x
--   where
--     lem : (x : X) → (id ∙ shift x) ≈ (shift x ∙ id)
--     lem x x' = yield refl λ where .force → lem x'
