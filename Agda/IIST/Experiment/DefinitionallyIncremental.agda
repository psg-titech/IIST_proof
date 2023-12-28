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

  ⟨_⟩-IST : ℕ → Set → Set → Set
  ⟨ d ⟩-IST X Y = X → Step d X Y

  data Step (d : ℕ) (X Y : Set) : Set where
    fail : Step d X Y
    next : ∀ {d'} → d ≡ suc d' → ∞⟨ d' ⟩-IST X Y → Step d X Y
    yield : d ≡ 0 → Y → ∞⟨ 0 ⟩-IST X Y → Step d X Y

  record ∞⟨_⟩-IST (d : ℕ) (X Y : Set) : Set where
    coinductive
    field force : ⟨ d ⟩-IST X Y

open ∞⟨_⟩-IST

pattern next! f = next refl f
pattern yield! y f = yield refl y f

feed : ∀ {d} → ⟨ d ⟩-IST X Y → List X → Maybe (List Y)
feed f [] = just []
feed f (x ∷ xs) with f x
... | fail = nothing
... | next! f' = feed (force f') xs
... | yield! y f' = Maybe.map (y ∷_) (feed (force f') xs)

--------------------------------------------------------------------------------
-- Semantics

id : ⟨ 0 ⟩-IST X X
id x = yield! x λ where .force → id

shift : X → ⟨ 0 ⟩-IST X X
shift x y = yield! x λ where .force → shift y

unshift : {{_ : Eq X}} → X → ⟨ 1 ⟩-IST X X
unshift x y with x ≟ y
... | no _ = fail
... | yes refl = next! λ where .force → id

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ⟨ 0 ⟩-IST X Y
F-map-fold a f g x with f a .to x
... | nothing = fail
... | just y = yield! y λ where .force → F-map-fold (g a x) f g

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ⟨ 0 ⟩-IST Y X
B-map-fold a f g y with f a .from y
... | nothing = fail
... | just x = yield! x λ where .force → B-map-fold (g a x) f g

_∙_ : ∀ {d d'} → ⟨ d ⟩-IST X Y → ⟨ d' ⟩-IST Y Z → ⟨ d + d' ⟩-IST X Z
(f ∙ g) x with f x
... | fail = fail
... | next! f' = next! λ where .force → force f' ∙ g
... | yield! y f' with g y
...   | fail = fail
...   | next! g' = next! λ where .force → force f' ∙ force g'
...   | yield! z g' = yield! z λ where .force → force f' ∙ force g'

later : ∀ {d} → ⟨ d ⟩-IST X Y → ⟨ suc d ⟩-IST X Y
later f x = next! λ where .force → shift x ∙ f

_∥_ : ∀ {d d'} → ⟨ d ⟩-IST X Y → ⟨ d' ⟩-IST Z W → ⟨ d ⊔ d' ⟩-IST (X × Z) (Y × W)
(f ∥ g) (x , z) with f x | g z
... | fail        | _           = fail
... | _           | fail        = fail
... | next! f'    | next! g'    = next! λ where .force → force f' ∥ force g'
... | next! f'    | yield! _ _  = next (cong suc (sym (⊔-identityʳ _))) λ where .force → force f' ∥ (shift z ∙ g)
... | yield! _ _  | next! g'    = next! λ where .force → (shift x ∙ f) ∥ force g'
... | yield! y f' | yield! w g' = yield! (y , w) λ where .force → force f' ∥ force g'

F⟦_⟧ : (e : E X Y) → ⟨ DF⟦ e ⟧ ⟩-IST X Y
F⟦ map-fold a f g ⟧ = F-map-fold a f g
F⟦ delay x ⟧ = shift x
F⟦ hasten x ⟧ = unshift x
F⟦ e ⟫ e' ⟧ = F⟦ e ⟧ ∙ F⟦ e' ⟧
F⟦ e ⊗ e' ⟧ = F⟦ e ⟧ ∥ F⟦ e' ⟧

B⟦_⟧ : (e : E X Y) → ⟨ DB⟦ e ⟧ ⟩-IST Y X
B⟦ map-fold a f g ⟧ = B-map-fold a f g
B⟦ delay x ⟧ = unshift x
B⟦ hasten x ⟧ = shift x
B⟦ e ⟫ e' ⟧ = B⟦ e' ⟧ ∙ B⟦ e ⟧
B⟦ e ⊗ e' ⟧ = B⟦ e ⟧ ∥ B⟦ e' ⟧

--------------------------------------------------------------------------------
-- Bisimulation

mutual

  _≈_ : ∀ {d₁ d₂} → ⟨ d₁ ⟩-IST X Y → ⟨ d₂ ⟩-IST X Y → Set
  f ≈ g = ∀ x → f x Step≈ g x

  data _Step≈_ {X Y : Set} {d₁ d₂ : ℕ} : Step d₁ X Y → Step d₂ X Y → Set where
    ≈fail : d₁ ≡ d₂ → fail Step≈ fail
    ≈next : ∀ {d₁' d₂'} {f : ∞⟨ d₁' ⟩-IST X Y} {g : ∞⟨ d₂' ⟩-IST X Y}
      → d₁ ≡ d₂
      → (p : d₁ ≡ suc d₁')
      → (q : d₂ ≡ suc d₂')
      → f ∞≈ g
      → next p f Step≈ next q g
    ≈yield : ∀ {x y f g}
      → (p : d₁ ≡ 0)
      → (q : d₂ ≡ 0)
      → x ≡ y
      → f ∞≈ g
      → yield p x f Step≈ yield q y g

  record _∞≈_ {d d'} (f : ∞⟨ d ⟩-IST X Y) (g : ∞⟨ d' ⟩-IST X Y): Set where
    coinductive
    field force : force f ≈ force g

open _∞≈_

pattern ≈fail! = ≈fail refl
pattern ≈next! f≈g = ≈next refl refl refl f≈g
pattern ≈yield! x≡y f≈g = ≈yield refl refl x≡y f≈g

≈-refl : ∀ {d} {f : ⟨ d ⟩-IST X Y} → f ≈ f
≈-refl {f = f} x with f x
... | fail = ≈fail!
... | next! f' = ≈next! λ where .force → ≈-refl
... | yield! y f' = ≈yield! refl λ where .force → ≈-refl

≈-sym : ∀ {d} {f g : ⟨ d ⟩-IST X Y} → f ≈ g → g ≈ f
≈-sym {f = f} {g = g} f≈g x with f x | g x | f≈g x
... | fail | fail | ≈fail! = ≈fail!
... | next! _ | next! _ | ≈next! f'≈g' =
      ≈next! λ where .force → ≈-sym (force f'≈g')
... | yield! _ _ | yield! _ _ | ≈yield! refl f'≈g' =
      ≈yield! refl λ where .force → ≈-sym (force f'≈g')

≈-trans : ∀ {d} {f g h : ⟨ d ⟩-IST X Y} → f ≈ g → g ≈ h → f ≈ h
≈-trans {f = f} {g = g} {h = h} f≈g g≈h x with f x | g x | h x | f≈g x | g≈h x
... | fail | fail | fail | ≈fail! | ≈fail! = ≈fail!
... | next! _ | next! _ | next! _ | ≈next! f'≈g' | ≈next! g'≈h' =
      ≈next! λ where .force → ≈-trans (force f'≈g') (force g'≈h')
... | yield! _ _ | yield! _ _ | yield! _ _ | ≈yield! refl f'≈g' | ≈yield! refl g'≈h' =
      ≈yield! refl λ where .force → ≈-trans (force f'≈g') (force g'≈h')

≈-feed : ∀ {d} {f g : ⟨ d ⟩-IST X Y}
  → f ≈ g
  → ∀ xs → feed f xs ≡ feed g xs
≈-feed f≈g [] = refl
≈-feed {f = f} {g} f≈g (x ∷ xs) with f x | g x | f≈g x
... | fail | fail | ≈fail! = refl
... | next! _ | next! _ | ≈next! f'≈g'
      rewrite ≈-feed (force f'≈g') xs = refl
... | yield! _ _ | yield! _ _ | ≈yield! refl f'≈g'
      rewrite ≈-feed (force f'≈g') xs = refl

--------------------------------------------------------------------------------

F∘I≈B : ∀ (e : E X Y) → F⟦ I⟦ e ⟧ ⟧ ≈ B⟦ e ⟧
F∘I≈B (map-fold a f g) y with f a .from y
... | nothing = ≈fail!
... | just x = ≈yield! refl λ where .force → {!   !}
F∘I≈B (delay x) = ≈-refl
F∘I≈B (hasten x) = ≈-refl
F∘I≈B (e ⟫ e') z with F⟦ I⟦ e' ⟧ ⟧ z | B⟦ e' ⟧ z | F∘I≈B e' z
... | fail | fail | ≈fail _ = ≈fail (DF∘I≡DB (e ⟫ e'))
... | next _ _ | next _ _ | ≈next _ _ _ ih = {!   !}
... | yield _ _ _ | yield _ _ _ | ≈yield _ _ ih₁ ih₂ = {!   !}
F∘I≈B (e ⊗ e') (y , w) = {!   !}

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
