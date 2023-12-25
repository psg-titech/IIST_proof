{-# OPTIONS --guardedness #-}

-- Tested with agda 2.6.4 and agda-stdlib 2.0

module IIST-inf where

open import Data.Maybe.Base using ( Maybe; just; nothing )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Product.Base as Prod using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Function using ( _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans )
open import Relation.Binary.Structures using ( IsDecEquivalence )
open import Relation.Binary.TypeClasses using ( _≟_ )
open import Relation.Nullary using ( ¬_; yes; no )

open import IIST.Common
open _⇌_

private
  variable
    A B X Y Z W : Set

-------------------------------------------------------------------------------
-- Colist

mutual

  data Colist (A : Set) : Set where
    [] : Colist A
    _∷_ : A → ∞Colist A → Colist A

  record ∞Colist (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : Colist A

open ∞Colist

-- η is safe for ∞Colist as η expansion is blocked by the choice of the constuctors of Colist
{-# ETA ∞Colist #-}

-------------------------------------------------------------------------------
-- Fallible Colist

mutual

  data FallibleColist (A : Set) : Set where
    [] : FallibleColist A
    fail : FallibleColist A
    _∷_ : A → ∞FallibleColist A → FallibleColist A

  record ∞FallibleColist (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : FallibleColist A

open ∞FallibleColist

-- η is safe as the same reason as ∞Colist
{-# ETA ∞FallibleColist #-}

map : (A → B) → FallibleColist A → FallibleColist B
map f [] = []
map f fail = fail
map f (x ∷ xs) = f x ∷ λ where .force → map f (force xs)

shift : A → FallibleColist A → FallibleColist A
shift x [] = []
shift x fail = x ∷ λ where .force → fail
shift x (y ∷ xs) = x ∷ λ where .force → shift y (force xs)

unshift : {{_ : Eq A}} → A → FallibleColist A → FallibleColist A
unshift x [] = []
unshift x fail = fail
unshift x (y ∷ xs) with x ≟ y
... | no _ = fail
... | yes _ = force xs

zip : FallibleColist A → FallibleColist B → FallibleColist (A × B)
zip fail _ = fail
zip _ fail = fail
zip [] _ = []
zip _ [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ λ where .force → zip (force xs) (force ys)

unzipₗ : FallibleColist (A × B) → FallibleColist A
unzipₗ = map proj₁

unzipᵣ : FallibleColist (A × B) → FallibleColist B
unzipᵣ = map proj₂

-------------------------------------------------------------------------------
-- Fallible Conat

mutual

  data FallibleCoℕ : Set where
    zero : FallibleCoℕ
    fail : FallibleCoℕ
    suc : ∞FallibleCoℕ → FallibleCoℕ

  record ∞FallibleCoℕ : Set where
    coinductive
    field
      force : FallibleCoℕ

open ∞FallibleCoℕ

_∸ℕ_ : FallibleCoℕ → ℕ → FallibleCoℕ
m ∸ℕ zero = m
zero ∸ℕ suc n = zero
fail ∸ℕ suc n = fail
suc m ∸ℕ suc n = force m ∸ℕ n

colength : Colist A → FallibleCoℕ
colength [] = zero
colength (x ∷ xs) = suc λ where .force → colength (force xs)

fallibleColength : FallibleColist A → FallibleCoℕ
fallibleColength [] = zero
fallibleColength fail = fail
fallibleColength (x ∷ xs) = suc λ where .force → fallibleColength (force xs)

--------------------------------------------------------------------------------
-- Bisimilarity

mutual

  data FallibleCoℕBisim : (m n : FallibleCoℕ) → Set where
    zero : FallibleCoℕBisim zero zero
    fail : FallibleCoℕBisim fail fail
    suc : ∀ {m n} → ∞FallibleCoℕBisim m n → FallibleCoℕBisim (suc m) (suc n)

  record ∞FallibleCoℕBisim (m n : ∞FallibleCoℕ) : Set where
    coinductive
    field
      force : FallibleCoℕBisim (force m) (force n)

open ∞FallibleCoℕBisim

-------------------------------------------------------------------------------
-- No fail

mutual

  data NoFail {A : Set} : FallibleColist A → Set where
    [] : NoFail []
    _∷_ : ∀ x {xs} → ∞NoFail xs → NoFail (x ∷ xs)

  record ∞NoFail (xs : ∞FallibleColist A) : Set where
    coinductive
    field
      force : NoFail (force xs)

open ∞NoFail

fromColist : Colist A → FallibleColist A
fromColist [] = []
fromColist (x ∷ xs) = x ∷ λ where .force → fromColist (force xs)

NoFail-fromColist : ∀ {xs : Colist A} → NoFail (fromColist xs)
NoFail-fromColist {xs = []} = []
NoFail-fromColist {xs = x ∷ xs} = x ∷ λ where .force → NoFail-fromColist

toColist : ∀ {xs : FallibleColist A} → NoFail xs → Colist A
toColist [] = []
toColist (x ∷ xs) = x ∷ λ where .force → toColist (force xs)

-------------------------------------------------------------------------------
-- Prefix

mutual

  data _≺_ {A : Set} : FallibleColist A → FallibleColist A → Set where
    [] : ∀ {xs} → [] ≺ xs
    fail : fail ≺ fail
    _∷_ : ∀ x {xs ys} → xs ∞≺ ys → (x ∷ xs) ≺ (x ∷ ys)

  record _∞≺_ (xs ys : ∞FallibleColist A) : Set where
    coinductive
    field
      force : force xs ≺ force ys

open _∞≺_

≺-refl : ∀ {xs : FallibleColist A} → xs ≺ xs
≺-refl {xs = []} = []
≺-refl {xs = fail} = fail
≺-refl {xs = x ∷ xs} = x ∷ λ where .force → ≺-refl

≺-trans : ∀ {xs ys zs : FallibleColist A}
  → xs ≺ ys
  → ys ≺ zs
  → xs ≺ zs
≺-trans [] ys≺zs = []
≺-trans fail fail = fail
≺-trans (x ∷ xs≺ys) (.x ∷ ys≺zs) = x ∷ λ where .force → ≺-trans (force xs≺ys) (force ys≺zs)

shift-≺-∷ : ∀ (x : A) xs → (shift x xs) ≺ (x ∷ delay xs)
shift-≺-∷ x [] = []
shift-≺-∷ x fail = x ∷ λ where .force → fail
shift-≺-∷ x (y ∷ xs) = x ∷ λ where .force → shift-≺-∷ y (force xs)

≺-shift : ∀ (x : A) {xs ys} → xs ≺ ys → shift x xs ≺ shift x ys
≺-shift x [] = []
≺-shift x fail = x ∷ λ where .force → fail
≺-shift x (y ∷ xs≺ys) = x ∷ λ where .force → ≺-shift y (force xs≺ys)

≺-unshift : ∀ {{_ : Eq A}} (x : A) {xs ys} → xs ≺ ys → unshift x xs ≺ unshift x ys
≺-unshift x [] = []
≺-unshift x fail = fail
≺-unshift x (y ∷ xs≺ys) with x ≟ y
... | no _ = fail
... | yes _ = force xs≺ys

≺-zip : ∀ {xs xs' : FallibleColist A} {ys ys' : FallibleColist B}
  → xs' ≺ xs
  → ys' ≺ ys
  → zip xs' ys' ≺ zip xs ys
≺-zip {xs = []} [] fail = fail
≺-zip {xs = fail} [] fail = fail
≺-zip {xs = _ ∷ _} [] fail = fail
≺-zip [] [] = []
≺-zip [] (_ ∷ _) = []
≺-zip fail ys'≺ys = fail
≺-zip (x ∷ xs'≺xs) [] = []
≺-zip (x ∷ xs'≺xs) fail = fail
≺-zip (x ∷ xs'≺xs) (y ∷ ys'≺ys) = (x , y) ∷ λ where .force → ≺-zip (force xs'≺xs) (force ys'≺ys)

≺-unzipₗ : ∀ {xys' xys : FallibleColist (A × B)}
  → xys' ≺ xys
  → unzipₗ xys' ≺ unzipₗ xys
≺-unzipₗ [] = []
≺-unzipₗ fail = fail
≺-unzipₗ ((x , y) ∷ xys'≺xys) = x ∷ λ where .force → ≺-unzipₗ (force xys'≺xys)

≺-unzipᵣ : ∀ {xys' xys : FallibleColist (A × B)}
  → xys' ≺ xys
  → unzipᵣ xys' ≺ unzipᵣ xys
≺-unzipᵣ [] = []
≺-unzipᵣ fail = fail
≺-unzipᵣ ((x , y) ∷ xys'≺xys) = y ∷ λ where .force → ≺-unzipᵣ (force xys'≺xys)

-------------------------------------------------------------------------------
-- Sequence transformation

ST : Set → Set → Set
ST X Y = FallibleColist X → FallibleColist Y

IsIncremental : ST X Y → Set
IsIncremental st = ∀ {xs xs'}
  → xs' ≺ xs
  → st xs' ≺ st xs

HasDelay : ℕ → ST X Y → Set
HasDelay d st = ∀ xs →
  FallibleCoℕBisim
    (fallibleColength (st xs))
    (fallibleColength xs ∸ℕ d)

-------------------------------------------------------------------------------
-- IIST constructors and semantics

infixr 9 _⟫_
infixr 3 _⊗_

data E : Set → Set → Set₁ where
  map-fold : A → (A → X ⇌ Y) → (A → X → A) → E X Y
  delay : {{_ : Eq X}} → X → E X X
  hasten : {{_ : Eq X}} → X → E X X
  _⟫_ : E X Y → E Y Z → E X Z
  _⊗_ : E X Y → E Z W → E (X × Z) (Y × W)

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST X Y
F-map-fold a f g [] = []
F-map-fold a f g fail = fail
F-map-fold a f g (x ∷ xs) with f a .to x
... | nothing = fail
... | just y = y ∷ λ where .force → F-map-fold (g a x) f g (force xs)

F⟦_⟧ : E X Y → ST X Y
F⟦ map-fold a f g ⟧ = F-map-fold a f g
F⟦ delay x ⟧ = shift x
F⟦ hasten x ⟧ = unshift x
F⟦ e ⟫ e' ⟧ = F⟦ e' ⟧ ∘ F⟦ e ⟧
F⟦ e ⊗ e' ⟧ xzs = zip (F⟦ e ⟧ (unzipₗ xzs)) (F⟦ e' ⟧ (unzipᵣ xzs))

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST Y X
B-map-fold a f g [] = []
B-map-fold a f g fail = fail
B-map-fold a f g (y ∷ ys) with f a .from y
... | nothing = fail
... | just x = x ∷ λ where .force → B-map-fold (g a x) f g (force ys)

B⟦_⟧ : E X Y → ST Y X
B⟦ map-fold a f g ⟧ = B-map-fold a f g
B⟦ delay x ⟧ = unshift x
B⟦ hasten x ⟧ = shift x
B⟦ e ⟫ e' ⟧ = B⟦ e ⟧ ∘ B⟦ e' ⟧
B⟦ e ⊗ e' ⟧ xzs = zip (B⟦ e ⟧ (unzipₗ xzs)) (B⟦ e' ⟧ (unzipᵣ xzs))

D⟦_⟧ : E X Y → ℕ × ℕ
D⟦ map-fold a f g ⟧ = 0 , 0
D⟦ delay x ⟧ = 0 , 1
D⟦ hasten x ⟧ = 1 , 0
D⟦ e ⟫ e' ⟧ =
  let d₁ , d₁' = D⟦ e ⟧
      d₂ , d₂' = D⟦ e' ⟧
   in d₁ + d₂ , d₁' + d₂'
D⟦ e ⊗ e' ⟧ =
  let d₁ , d₁' = D⟦ e ⟧
      d₂ , d₂' = D⟦ e' ⟧
   in d₁ ⊔ d₂ , d₁' ⊔ d₂'

DF⟦_⟧ DB⟦_⟧ : E X Y → ℕ
DF⟦ e ⟧ = proj₁ D⟦ e ⟧
DB⟦ e ⟧ = proj₂ D⟦ e ⟧

--------------------------------------------------------------------------------

F-incremental : ∀ (e : E X Y) → IsIncremental F⟦ e ⟧
F-incremental (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → IsIncremental F⟦ map-fold a f g ⟧
    helper a [] = []
    helper a fail = fail
    helper a (x ∷ xs'≺xs) with f a .to x
    ... | nothing = fail
    ... | just y = y ∷ λ where .force → helper (g a x) (force xs'≺xs)
F-incremental (delay x) = ≺-shift x
F-incremental (hasten x) = ≺-unshift x
F-incremental (e ⟫ e') = F-incremental e' ∘ F-incremental e
F-incremental (e ⊗ e') xzs'≺xzs =
  ≺-zip (F-incremental e (≺-unzipₗ xzs'≺xzs)) (F-incremental e' (≺-unzipᵣ xzs'≺xzs))

B-incremental : ∀ (e : E X Y) → IsIncremental B⟦ e ⟧
B-incremental (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → IsIncremental B⟦ map-fold a f g ⟧
    helper a [] = []
    helper a fail = fail
    helper a (y ∷ ys'≺ys) with f a .from y
    ... | nothing = fail
    ... | just x = x ∷ λ where .force → helper (g a x) (force ys'≺ys)
B-incremental (delay x) = ≺-unshift x
B-incremental (hasten x) = ≺-shift x
B-incremental (e ⟫ e') = B-incremental e ∘ B-incremental e'
B-incremental (e ⊗ e') yws'≺yws =
  ≺-zip (B-incremental e (≺-unzipₗ yws'≺yws)) (B-incremental e' (≺-unzipᵣ yws'≺yws))

F-delay : ∀ (e : E X Y) → HasDelay DF⟦ e ⟧ F⟦ e ⟧
F-delay (map-fold a f g) = {!   !}
F-delay (delay x) [] = zero
F-delay (delay x) fail = {!   !}
F-delay (delay x) (y ∷ xs) = {!   !}
F-delay (hasten x) = {!   !}
F-delay (e ⟫ e') xs =
  let ih = F-delay e xs
      ih' = F-delay e' (F⟦ e ⟧ xs)
   in {!   !}
F-delay (e ⊗ e') = {!   !}
