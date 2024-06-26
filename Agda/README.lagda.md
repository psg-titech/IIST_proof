# Formalization of IISTs in Agda

This directory contains a mechanized formalization of Invertible Incremental Sequence Transformations (IISTs) by Shirai et al.
<https://jssst.or.jp/files/user/taikai/2023/papers/15-R-S.pdf> (in Japanese)

We are trying to formalize IISTs in three ways:
- IISTs as partial functions on lists
- IISTs as partial functions on colists
- IISTs as mealy-ish machines

## Environment

- agda 2.6.4
- agda-stdlib 2.0

```agda
module README where

import Level
open import Data.List using ( List; []; _∷_; length; zip; unzip )
open import Data.Maybe using ( Maybe; just; nothing; _>>=_; maybe )
open import Data.Maybe.Effectful using () renaming ( monad to monadMaybe )
open import Data.Nat using ( ℕ; zero; suc; _+_; _∸_; _≤?_; _⊔_ )
open import Data.Product using ( ∃-syntax; _×_; _,_; proj₁; proj₂ )
open import Effect.Monad using ( RawMonad )
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures
open import Relation.Binary.TypeClasses using ( _≟_ )
open import Relation.Nullary

open RawMonad {Level.zero} monadMaybe using ( _>=>_; _<$>_; _<*>_; pure )

private
  variable
    A B X Y Z W : Set
```

## What are IISTs?

An IIST is a kind of "invertible" list/stream processor.
It produces more output as more input is provided, and has an inverse processor that can recover more elements of the original input as more outputs are given.

Why do we need the notion of invertible computation at all? What does it do for us?
Like parsing and printing, or compression and decompression, there are many pairs of computations that are inverses of each other.
If each is developed separately, it is possible that some inconsistencies are introduced between them.
This is where the notion of invertible computation comes in.
It allows us to develop both computations simultaneously, ensuring that they are consistent with each other.
The IIST framework aims to provide a fundamental theory of invertible computation specifically for stream processing.

### Definitions of IISTs

The following are formal definitions of IIST and related concepts.
Here we only consider IISTs as partial functions on lists.

A *Sequence Transformation* (ST) is a partial function on lists.
```agda
ST : Set → Set → Set
ST X Y = List X → Maybe (List Y)
```
An ST `st` is an *Incremental* ST (IST) if it preserves the prefix relation. That is, if `st` produces an output `ys` for some input `xs`, any prefix of `st` will produce a prefix of `ys`.
```agda
infix 4 _≺_

-- xs ≺ ys means xs is a prefix of ys
data _≺_ {A : Set} : List A → List A → Set where
  [] : ∀ {xs} → [] ≺ xs
  _∷_ : ∀ x {xs ys} → xs ≺ ys → x ∷ xs ≺ x ∷ ys

IsIncremental : ST X Y → Set
IsIncremental st = ∀ {xs' xs ys}
  → xs' ≺ xs
  → st xs ≡ just ys
  → ∃[ ys' ] (ys' ≺ ys) × (st xs' ≡ just ys')
```
An ST `st` is an *d-Incremental* ST (d-IST), if it is incremental and the length of output is always `d` less than the length of input.
```agda
HasDelay : ℕ → ST X Y → Set
HasDelay d st = ∀ xs {ys}
  → st xs ≡ just ys
  → length ys ≡ length xs ∸ d

record Is_-IST_ (d : ℕ) (st : ST X Y) : Set where
  field
    isIncremental : IsIncremental st
    hasDelay : HasDelay d st
```
An ST `st` is an *Inverse* IST (IIST) of another ST `st'`, when `st'` outputs `ys` for some `xs`, `st` recovers a prefix of `xs` from `ys`.
Specifically, `st` is a *d-Inverse* IST (d-IIST) of `st'`, if `st` can always recover the original input of `st'` except for the last `d` elements.
The notion of inverse here is a relaxed version of the usual inverse. We believe this is unique to IISTs.
```agda
_IsIISTOf_ : ST X Y → ST Y X → Set
st' IsIISTOf st = ∀ {xs ys}
  → st xs ≡ just ys
  → ∃[ xs' ] (xs' ≺ xs) × (st' ys ≡ just xs')

record _Is_-IISTOf_ (st' : ST X Y) (d : ℕ) (st : ST Y X) : Set where
  field
    is-d-IST : Is d -IST st'
    isIIST : st' IsIISTOf st
```
An ST `st` is an *(d, d')-Invertible* IST ((d, d')-IIST) if it is d-incremental and there exists a d'-IIST of it.
```agda
record Is⟨_,_⟩-IIST_ (d d' : ℕ) (st : ST X Y) : Set where
  field
    inverse : ST Y X
    is-d-IST : Is d -IST st
    inverse-is-d'-IIST : inverse Is d' -IISTOf st
```

Cumlative sum is a simple example of (0, 0)-IIST.
```agda
cumSum : ℕ → ST ℕ ℕ
cumSum acc [] = pure []
cumSum acc (x ∷ xs) = ((acc + x) ∷_) <$> cumSum (acc + x) xs

cumSumInv : ℕ → ST ℕ ℕ
cumSumInv acc [] = pure []
cumSumInv acc (x ∷ xs) with suc x ≤? acc
... | no _ = ((x ∸ acc) ∷_) <$> cumSumInv x xs
... | yes _ = nothing

_ : cumSum 0 (1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 3 ∷ 6 ∷ [])
_ = refl

_ : cumSumInv 0 (1 ∷ 3 ∷ 6 ∷ []) ≡ just (1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : cumSumInv 0 (3 ∷ 2 ∷ 1 ∷ []) ≡ nothing
_ = refl
```

### A Langauge for IISTs

It turned out that any (d, d')-IIST can be expressed as a term of the `E` datatype defined below. This is one of the properties we are trying to mechanically prove.
```agda
-- Invertible partial function
record _⇌_ (A B : Set) : Set where
  field
    to : A → Maybe B
    from : B → Maybe A
    to→from : ∀ {x y} → to x ≡ just y → from y ≡ just x
    from→to : ∀ {x y} → from y ≡ just x → to x ≡ just y

  inverse : B ⇌ A
  to inverse = from
  from inverse = to
  to→from inverse = from→to
  from→to inverse = to→from

open _⇌_

infixr 9 _`⋙_
infixr 3 _`⊗_

Eq : Set → Set
Eq A = IsDecEquivalence {A = A} _≡_ -- Discrete

data E : Set → Set → Set₁ where
  -- Inseparable into map and fold!
  `map-fold : A → (A → X ⇌ Y) → (A → X → A) → E X Y
  -- Delay the output by one step. The argument is the initial value.
  `delay : {{_ : Eq X}} → X → E X X
  -- The inverse of `delay`.
  `hasten : {{_ : Eq X}} → X → E X X
  -- Sequential composition.
  _`⋙_ : E X Y → E Y Z → E X Z
  -- Parallel composition.
  _`⊗_ : E X Y → E Z W → E (X × Z) (Y × W)
```
`F⟦-⟧` and `B⟦-⟧` are forward and backward semantics of `E` terms, respectively.
```agda
shift : X → List X → List X
shift _ [] = []
shift x (y ∷ xs) = x ∷ shift y xs

unshift : {{_ : Eq X}} → X → ST X X
unshift x [] = just []
unshift x (x' ∷ xs) with x ≟ x'
... | yes _ = just xs
... | no _ = nothing

_⊗_ : ST X Y → ST Z W → ST (X × Z) (Y × W)
(f ⊗ g) xzs =
  let xs , zs = unzip xzs
   in (| zip (f xs) (g zs) |)

-- Forward semantics
F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST X Y
F-map-fold a f g [] = just []
F-map-fold a f g (x ∷ xs) = (| f a .to x ∷ F-map-fold (g a x) f g xs |)

F⟦_⟧ : E X Y → ST X Y
F⟦ `map-fold a f g ⟧ = F-map-fold a f g
F⟦ `delay x ⟧ = just ∘ shift x
F⟦ `hasten x ⟧ = unshift x
F⟦ e `⋙ e' ⟧ = F⟦ e ⟧ >=> F⟦ e' ⟧
F⟦ e `⊗ e' ⟧ = F⟦ e ⟧ ⊗ F⟦ e' ⟧

-- Backward semantics
B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST Y X
B-map-fold a f g [] = just []
B-map-fold a f g (y ∷ ys) = do
  x ← f a .from y
  (x ∷_) <$> B-map-fold (g a x) f g ys

B⟦_⟧ : E X Y → ST Y X
B⟦ `map-fold a f g ⟧ = B-map-fold a f g
B⟦ `delay x ⟧ = unshift x
B⟦ `hasten x ⟧ = just ∘ shift x
B⟦ e `⋙ e' ⟧ = B⟦ e' ⟧ >=> B⟦ e ⟧
B⟦ e `⊗ e' ⟧ = B⟦ e ⟧ ⊗ B⟦ e' ⟧
```
`F⟦ e ⟧` and `B⟦ e ⟧` are mechanically proved to be an (`DF⟦ e ⟧`, `DB⟦ e ⟧`)-IIST and an (`DB⟦ e ⟧`, `DF⟦ e ⟧`)-IIST, respectively, for any `E` term `e` where the inverse of `F⟦ e ⟧` is `B⟦ e ⟧` and vice versa.
```agda
D⟦_⟧ : E X Y → ℕ × ℕ
D⟦ `map-fold a f g ⟧ = 0 , 0
D⟦ `delay x ⟧ = 0 , 1
D⟦ `hasten x ⟧ = 1 , 0
D⟦ e `⋙ e' ⟧ =
  let d₁ , d₁' = D⟦ e ⟧
      d₂ , d₂' = D⟦ e' ⟧
   in d₁ + d₂ , d₂' + d₁'
D⟦ e `⊗ e' ⟧ =
  let d₁ , d₁' = D⟦ e ⟧
      d₂ , d₂' = D⟦ e' ⟧
   in d₁ ⊔ d₂ , d₁' ⊔ d₂'

DF⟦_⟧ DB⟦_⟧ : E X Y → ℕ
DF⟦ e ⟧ = proj₁ D⟦ e ⟧
DB⟦ e ⟧ = proj₂ D⟦ e ⟧

F-IIST : ∀ (e : E X Y) → Is⟨ DF⟦ e ⟧ , DB⟦ e ⟧ ⟩-IIST F⟦ e ⟧
B-IIST : ∀ (e : E X Y) → Is⟨ DB⟦ e ⟧ , DF⟦ e ⟧ ⟩-IIST B⟦ e ⟧
```
We also have a function `I⟦-⟧` that "inverts" the semantics of `E` terms.
That is, `F⟦ I⟦ e ⟧ ⟧ ≡ B⟦ e ⟧` and `B⟦ I⟦ e ⟧ ⟧ ≡ F⟦ e ⟧`.
`I⟦-⟧` is not involutive though.
```agda
I⟦_⟧ : E X Y → E Y X
I⟦ `map-fold a f g ⟧ = `map-fold a (inverse ∘ f) (λ a → maybe (g a) a ∘ f a .from)
I⟦ `delay x ⟧ = `hasten x
I⟦ `hasten x ⟧ = `delay x
I⟦ e `⋙ e' ⟧ = I⟦ e' ⟧ `⋙ I⟦ e ⟧
I⟦ e `⊗ e' ⟧ = I⟦ e ⟧ `⊗ I⟦ e' ⟧
```
