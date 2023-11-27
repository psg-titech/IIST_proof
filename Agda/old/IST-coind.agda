{-# OPTIONS --guardedness #-}

open import Category.Monad using ( RawMonad )
open RawMonad {{...}} using ( _>>=_; return ) renaming ( _<=<_ to _∙_ )
open import Data.Bool using ( Bool; true; false; T )
open import Data.List using ( List; []; _∷_ )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Maybe.Categorical using ( monad )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Nat using ( ℕ; zero; suc; _+_; _∸_; _⊔_ )
open import Data.Product using ( _×_; _,_; proj₁; proj₂ )
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
    invertible : ∀ {x y} → to x ≡ just y ↔ from y ≡ just x

open _⇌_

-------------------------------------------------------------------------------
-- Eq typeclass

record Eq (A : Set) : Set where
  infix 4 _==_
  field
    _==_ : (x y : A) → Dec (x ≡ y)

open Eq {{...}}

-------------------------------------------------------------------------------
-- Incremental Sequence Transformation

mutual

  IST : Set → Set → Set
  IST X Y =  X ⇀ Step X Y

  data Step (X Y : Set) : Set where
    next : ∞IST X Y → Step X Y
    yield : Y → ∞IST X Y → Step X Y

  record ∞IST (X Y : Set) : Set where
    coinductive
    constructor delay
    field
      force : IST X Y

open ∞IST

yield-injective : ∀ {y y' : Y} {f f'} → yield {X = X} y f ≡ yield y' f' → y ≡ y'
yield-injective refl = refl

runIST : IST X Y → List X ⇀ List Y
runIST _ [] = return []
runIST f (x ∷ xs) with f x
... | nothing = nothing
... | just (next f') = runIST (f' .force) xs
... | just (yield y f') = do
        ys ← runIST (f' .force) xs
        return (y ∷ ys)

id : IST X X
id x = just $ yield x λ where .force → id

compose : IST X Y → IST Y Z → IST X Z
compose f g x with f x
... | nothing = nothing
... | just (next f') =
      just $ next λ where .force → compose (f' .force) g
... | just (yield y f') with g y
...   | nothing = nothing
...   | just (next g') =
        just $ next λ where .force → compose (f' .force) (g' .force)
...   | just (yield z g') =
        just $ yield z λ where .force → compose (f' .force) (g' .force)

parallel : IST X Y → IST Z W → IST (X × Z) (Y × W)
parallel = sub
  where
    sub : IST X Y → IST Z W → IST (X × Z) (Y × W)
    waitY : List W → IST X Y → IST Z W → IST (X × Z) (Y × W)
    waitW : List Y → IST X Y → IST Z W → IST (X × Z) (Y × W)

    sub f g (x , z) with f x | g z
    ... | nothing | nothing = nothing
    ... | nothing | just _  = nothing
    ... | just _  | nothing = nothing
    ... | just (next f') | just (next g') =
          just $ next λ where .force → sub (f' .force) (g' .force)
    ... | just (next f') | just (yield w g') =
          just $ next λ where .force → waitY (w ∷ []) (f' .force) (g' .force)
    ... | just (yield y f') | just (next g') =
          just $ next λ where .force → waitW (y ∷ []) (f' .force) (g' .force)
    ... | just (yield y f') | just (yield w g') =
          just $ yield (y , w) λ where .force → sub (f' .force) (g' .force)

    waitY [] f g = sub f g
    waitY (w ∷ ws) f g (x , z) with f x | g z
    ... | nothing | nothing = nothing
    ... | nothing | just _  = nothing
    ... | just _  | nothing = nothing
    ... | just (next f') | just (next g') =
          just $ next λ where .force → sub (f' .force) (g' .force)
    ... | just (next f') | just (yield w g') =
          just $ next λ where .force → waitY (w ∷ []) (f' .force) (g' .force)
    ... | just (yield y f') | just (next g') =
          just $ next λ where .force → waitW (y ∷ []) (f' .force) (g' .force)
    ... | just (yield y f') | just (yield w g') =
          just $ yield (y , w) λ where .force → sub (f' .force) (g' .force)

    waitW [] f g = sub f g
    waitW (y ∷ ys) f g = {!   !}

