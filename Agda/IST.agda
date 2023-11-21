{-# OPTIONS --guardedness #-}

module IST where

open import Category.Monad using ( RawMonad )
open RawMonad {{...}} using ( _>>=_; return ) renaming ( _<=<_ to _∙_ )
open import Data.Bool using ( Bool; true; false; T )
open import Data.List using ( List; []; _∷_ )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Maybe.Categorical using ( monad )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Nat using ( ℕ; zero; suc; _+_; _∸_; _⊔_ )
open import Data.Nat.Properties using ( 0∸n≡0; +-∸-assoc; +-suc; _≤?_; m≤n⇒m∸n≡0; ≰⇒> )
open import Data.Product using ( _×_; _,_; proj₁; proj₂ )
open import Data.Vec using ( Vec; []; _∷_ )
open import Function using ( _$_ )
open import Relation.Nullary using ( Dec; yes; no )
open import Relation.Binary.PropositionalEquality

private
  variable
    A X Y Z W : Set
    n d d' : ℕ

-------------------------------------------------------------------------------
-- Misc.

instance
  maybeMonad = monad

infix 0 _↔_
_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (Q → P)

-------------------------------------------------------------------------------
-- Partial function and Partial invertible function

infix 0 _⇀_
_⇀_ : Set → Set → Set
X ⇀ Y = X → Maybe Y

infix 0 _⇌_
record _⇌_ (X Y : Set) : Set where
  field
    to : X ⇀ Y
    from : Y ⇀ X
    invertible : ∀ x y → to x ≡ just y ↔ from y ≡ just x

open _⇌_

-------------------------------------------------------------------------------
-- Eq typeclass

record Eq (A : Set) : Set where
  infix 4 _==_
  field
    _==_ : (x y : A) → Dec (x ≡ y)

open Eq {{...}}

instance

  eqNat : Eq ℕ
  _==_ {{eqNat}} = Data.Nat.Properties._≟_

-------------------------------------------------------------------------------
-- Incremental Sequence Transformation

{-

newtype IST x y = IST { runIST :: x -> Step x y }
data Step x y
  = Yield y (IST x y)
  | Next (IST x y)

-}

mutual

  IST : Set → Set → ℕ → Set
  IST X Y d = X ⇀ Step X Y d

  data Step (X Y : Set) : ℕ → Set where
    next : ∞IST X Y d → Step X Y (suc d)
    yield : Y → ∞IST X Y d → Step X Y d

  record ∞IST (X Y : Set) (d : ℕ) : Set where
    coinductive
    constructor delay
    field
      force : IST X Y d

open ∞IST

yield-injective : ∀ {y y' : Y} {f f'} → yield {X = X} {d = d} y f ≡ yield y' f' → y ≡ y'
yield-injective refl = refl

runIST : IST X Y d → Vec X n ⇀ Vec Y (n ∸ d)
runIST {d = d} t [] rewrite 0∸n≡0 d = return []
runIST {d = d} t (_∷_ {n = n} x xs) with t x
... | nothing = nothing
... | just (next t') = runIST (t' .force) xs
... | just (yield y t') with d ≤? n
...   | no d≰n rewrite m≤n⇒m∸n≡0 (≰⇒> d≰n) = return []
...   | yes d≤n rewrite +-∸-assoc 1 d≤n = do
          ys ← runIST (t' .force) xs
          return (y ∷ ys)

id : IST X X 0
id x = just $ yield x λ where .force → id

compose : IST X Y d → IST Y Z d' → IST X Z (d + d')
compose {d = d} f g x with f x
... | nothing = nothing
... | just (next f') =
      just $ next λ where .force → compose (f' .force) g
... | just (yield y f') with g y
...   | nothing = nothing
...   | just (next {d = d'} g') rewrite +-suc d d' =
        just $ next λ where .force → compose (f' .force) (g' .force)
...   | just (yield z g') =
        just $ yield z λ where .force → compose (f' .force) (g' .force)

--------------------------------------------------------------------------------
-- Syntax

data E : ℕ → ℕ → Set → Set → Set₁ where
  map-fold : A → (A → X ⇌ Y) → (A → X → A) → E 0 0 X Y
  delay : {{_ : Eq X}} → X → E 0 1 X X
  hasten : {{_ : Eq X}} → X → E 1 0 X X
  _⟫_ : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Y Z
    → E (d₁ + d₂) (d₁' + d₂') X Z
  _⊗_ : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Z W
    → E (d₁ ⊔ d₂) (d₁' ⊔ d₂') (X × Z) (Y × W)

--------------------------------------------------------------------------------
-- Semantics

F⟦_⟧ : E d d' X Y → IST X Y d
F⟦ map-fold a f g ⟧ x with f a .to x
... | nothing = nothing
... | just y = just $ yield y λ where .force → F⟦ map-fold (g a x) f g ⟧

F⟦ delay x ⟧ y = just $ yield x λ where .force → F⟦ delay y ⟧

F⟦ hasten x ⟧ y with x == y
... | no _ = nothing
... | yes refl = just $ next λ where .force → id

F⟦ e ⟫ e' ⟧ = {!   !}

F⟦ e ⊗ e' ⟧ = {!   !}

B⟦_⟧ : E d d' X Y → IST Y X d'
B⟦ map-fold a f g ⟧ y with f a .from y
... | nothing = nothing
... | just x = just $ yield x λ where .force → B⟦ map-fold (g a x) f g ⟧

B⟦ delay x ⟧ y with x == y
... | no _ = nothing
... | yes refl = just $ next λ where .force → id

B⟦ hasten x ⟧ y = just $ yield x λ where .force → B⟦ hasten y ⟧

B⟦ e ⟫ e' ⟧ = {!   !}

B⟦ e ⊗ e' ⟧ = {!   !}

B∙F⟦_⟧ : E d d' X Y → IST X X (d + d')
B∙F⟦ e ⟧ = compose F⟦ e ⟧ B⟦ e ⟧

B∙F : ∀ (e : E d d' X Y) x {x' f} → B∙F⟦ e ⟧ x ≡ just (yield x' f) → x ≡ x'
B∙F (map-fold a f g) x p with f a .to x in eq
... | just y with f a .from y in eq₁
...   | just x' with f a .invertible x y .proj₁ eq | yield-injective (just-injective p)
...     | eq₂ | eq₃ rewrite eq₁ | just-injective eq₂ | eq₃ = refl
B∙F (delay x) y p with x == x | p
... | yes refl | ()
... | no _ | ()
B∙F (hasten x) y p with x == y | p
... | yes refl | ()
... | no _ | ()
B∙F (e ⟫ e') x p = {!   !}
B∙F (e ⊗ e') x p = {!   !}
