{-# OPTIONS --guardedness --cubical #-}

module IIST.Experiment.Cubical where

open import Cubical.Codata.Stream.Base using ( Stream )
open import Cubical.Data.List.Base using ( List; []; _∷_ )
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Nat.Properties using ( +-zero; +-assoc )
open import Cubical.Data.Sigma.Base using ( _×_; _,_; fst )
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using ( idfun; _∘_ )
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open Stream

private
  variable
    A B C D : Type

--------------------------------------------------------------------------------
-- d-Incremental Sequence Transformation

infixr 5 _⋙_

mutual

  record IST (A B : Type) (d : ℕ) : Type where
    coinductive
    field
      step : A → Step A B d

  data Step (A B : Type) : ℕ → Type where
    fail : ∀ {d} → Step A B d
    next : ∀ {d} (f : IST A B d) → Step A B (suc d)
    yield : (y : B) (f : IST A B zero) → Step A B zero

open IST

id : IST A A 0
step id x = yield x id

shift : A → IST A A 0
step (shift x) y = yield x (shift y)

_⋙_ : ∀ {d d'} → IST A B d → IST B C d' → IST A C (d + d')
step (f ⋙ g) x with step f x
... | fail = fail
... | next f' = next (f' ⋙ g)
... | yield y f' with step g y
...   | fail = fail
...   | next g' = next (f' ⋙ g')
...   | yield z g' = yield z (f' ⋙ g')

later : ∀ {d} → IST A B d → IST A B (suc d)
step (later f) x = next (shift x ⋙ f)

--------------------------------------------------------------------------------
-- Properties

⋙-identityₗ : ∀ {d} (f : IST A B d) → id ⋙ f ≡ f
step (⋙-identityₗ f i) x with step f x
... | fail = fail
... | next f' = next (⋙-identityₗ f' i)
... | yield y f' = yield y (⋙-identityₗ f' i)

⋙-identityᵣ : ∀ {d} (f : IST A B d) → PathP (λ i → IST A B (+-zero d i)) (f ⋙ id) f
step (⋙-identityᵣ f i) x with step f x
... | fail = fail
... | next f' = next (⋙-identityᵣ f' i)
... | yield y f' = yield y (⋙-identityᵣ f' i)

⋙-assoc : ∀ {d₁ d₂ d₃} (f : IST A B d₁) (g : IST B C d₂) (h : IST C D d₃)
  → PathP (λ i → IST A D (+-assoc d₁ d₂ d₃ i)) (f ⋙ g ⋙ h) ((f ⋙ g) ⋙ h)
step (⋙-assoc f g h i) x with step f x
... | fail = fail
... | next f' = next (⋙-assoc f' g h i)
... | yield y f' with step g y
...   | fail = fail
...   | next g' = next (⋙-assoc f' g' h i)
...   | yield z g' with step h z
...     | fail = fail
...     | next h' = next (⋙-assoc f' g' h' i)
...     | yield w h' = yield w (⋙-assoc f' g' h' i)

later-⋙ₗ : ∀ {d d'} (f : IST A B d) (g : IST B C d')
  → later f ⋙ g ≡ later (f ⋙ g)
step (later-⋙ₗ f g i) x = next (⋙-assoc (shift x) f g (~ i))
