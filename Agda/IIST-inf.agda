{-# OPTIONS --guardedness #-}

-- Tested with agda 2.6.4 and agda-stdlib 2.0

module IIST-inf where

open import Data.Maybe.Base using ( Maybe; just; nothing; maybe )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Product.Base as Prod using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Unit.Base using ( ⊤; tt )
open import Function using ( _∘_ )
open import Relation.Binary.Core using ( Rel )
open import Relation.Binary.Definitions using ( Reflexive )
open import Relation.Binary.PropositionalEquality using ( _≡_; _≢_; refl; sym; trans )
open import Relation.Binary.Structures using ( IsDecEquivalence )
open import Relation.Binary.TypeClasses using ( _≟_ )
open import Relation.Nullary using ( ¬_; yes; no )

open import IIST.Common

private
  variable
    A B X Y Z W : Set

-------------------------------------------------------------------------------
-- Fallible Colist

mutual

  data Colistˣ (A : Set) : Set where
    [] : Colistˣ A
    fail : Colistˣ A
    _∷_ : A → ∞Colistˣ A → Colistˣ A

  record ∞Colistˣ (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : Colistˣ A

open ∞Colistˣ

{-# ETA ∞Colistˣ #-}

drop : ℕ → Colistˣ A → Colistˣ A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) fail = fail
drop (suc n) (_ ∷ xs) = drop n (force xs)

map : (A → B) → Colistˣ A → Colistˣ B
map f [] = []
map f fail = fail
map f (x ∷ xs) = f x ∷ λ where .force → map f (force xs)

shift : A → Colistˣ A → Colistˣ A
shift x [] = []
shift x fail = x ∷ λ where .force → fail
shift x (y ∷ xs) = x ∷ λ where .force → shift y (force xs)

unshift : {{_ : Eq A}} → A → Colistˣ A → Colistˣ A
unshift x [] = []
unshift x fail = fail
unshift x (y ∷ xs) with x ≟ y
... | no _ = fail
... | yes _ = force xs

zip : Colistˣ A → Colistˣ B → Colistˣ (A × B)
zip fail _ = fail
zip _ fail = fail
zip [] _ = []
zip _ [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ λ where .force → zip (force xs) (force ys)

unzipₗ : Colistˣ (A × B) → Colistˣ A
unzipₗ = map proj₁

unzipᵣ : Colistˣ (A × B) → Colistˣ B
unzipᵣ = map proj₂

mutual

  data _Colistˣ≈_ {A : Set} : Colistˣ A → Colistˣ A → Set where
    [] : [] Colistˣ≈ []
    fail : fail Colistˣ≈ fail
    _∷_ : ∀ {x y xs ys} → x ≡ y → xs ∞Colistˣ≈ ys → (x ∷ xs) Colistˣ≈ (y ∷ ys)

  record _∞Colistˣ≈_ (xs ys : ∞Colistˣ A) : Set where
    coinductive
    field
      force : force xs Colistˣ≈ force ys

open _∞Colistˣ≈_


Colistˣ≈-refl : ∀ {xs : Colistˣ A} → xs Colistˣ≈ xs
Colistˣ≈-refl {xs = []} = []
Colistˣ≈-refl {xs = fail} = fail
Colistˣ≈-refl {xs = x ∷ xs} = refl ∷ λ where .force → Colistˣ≈-refl

Colistˣ≈-zip : ∀ {xs xs' : Colistˣ A} {ys ys' : Colistˣ B}
  → xs Colistˣ≈ xs'
  → ys Colistˣ≈ ys'
  → zip xs ys Colistˣ≈ zip xs' ys'
Colistˣ≈-zip [] [] = []
Colistˣ≈-zip [] fail = fail
Colistˣ≈-zip [] (_ ∷ _) = []
Colistˣ≈-zip fail [] = fail
Colistˣ≈-zip fail fail = fail
Colistˣ≈-zip fail (_ ∷ _) = fail
Colistˣ≈-zip (_ ∷ _) [] = []
Colistˣ≈-zip (_ ∷ _) fail = fail
Colistˣ≈-zip (refl ∷ xs≈xs') (refl ∷ ys≈ys') = refl ∷ λ where .force → Colistˣ≈-zip (force xs≈xs') (force ys≈ys')

-------------------------------------------------------------------------------
-- Fallible Conatural and its bisimilarity

mutual

  data Coℕˣ : Set where
    zero : Coℕˣ
    fail : Coℕˣ
    suc : ∞Coℕˣ → Coℕˣ

  record ∞Coℕˣ : Set where
    coinductive
    field
      force : Coℕˣ

open ∞Coℕˣ

{-# ETA ∞Coℕˣ #-}

_∸ℕ_ : Coℕˣ → ℕ → Coℕˣ
m ∸ℕ zero = m
zero ∸ℕ suc n = zero
fail ∸ℕ suc n = fail
suc m ∸ℕ suc n = force m ∸ℕ n


mutual

  data _Coℕˣ≈_ : Coℕˣ → Coℕˣ → Set where
    zero : zero Coℕˣ≈ zero
    failL : ∀ {n} → fail Coℕˣ≈ n
    failR : ∀ {n} → n Coℕˣ≈ fail
    suc : ∀ {m n} → m ∞Coℕˣ≈ n → suc m Coℕˣ≈ suc n

  record _∞Coℕˣ≈_ (m n : ∞Coℕˣ) : Set where
    coinductive
    field
      force : force m Coℕˣ≈ force n

open _∞Coℕˣ≈_

Coℕˣ≈-refl : ∀ {n : Coℕˣ} → n Coℕˣ≈ n
Coℕˣ≈-refl {zero} = zero
Coℕˣ≈-refl {fail} = failL
Coℕˣ≈-refl {suc n} = suc λ where .force → Coℕˣ≈-refl

Coℕˣ≈-sym : ∀ {m n : Coℕˣ} → m Coℕˣ≈ n → n Coℕˣ≈ m
Coℕˣ≈-sym zero = zero
Coℕˣ≈-sym failL = failR
Coℕˣ≈-sym failR = failL
Coℕˣ≈-sym (suc m≈n) = suc λ where .force → Coℕˣ≈-sym (force m≈n)

Coℕˣ≈-trans : ∀ {m n o : Coℕˣ}
  → m Coℕˣ≈ n
  → n Coℕˣ≈ o
  → m Coℕˣ≈ o
Coℕˣ≈-trans zero n≈o = n≈o
Coℕˣ≈-trans failL n≈o = failL
Coℕˣ≈-trans failR failL = {!   !}
Coℕˣ≈-trans failR failR = failR
Coℕˣ≈-trans (suc x) failR = failR
Coℕˣ≈-trans (suc m≈n) (suc n≈o) = suc λ where .force → Coℕˣ≈-trans (force m≈n) (force n≈o)

-------------------------------------------------------------------------------
-- Length

colengthˣ : Colistˣ A → Coℕˣ
colengthˣ [] = zero
colengthˣ fail = fail
colengthˣ (_ ∷ xs) = suc λ where .force → colengthˣ (force xs)

-------------------------------------------------------------------------------
-- Prefix

mutual

  data _≺_ {A : Set} : Colistˣ A → Colistˣ A → Set where
    [] : ∀ {xs} → [] ≺ xs
    fail : fail ≺ fail
    _∷_ : ∀ x {xs ys} → xs ∞≺ ys → (x ∷ xs) ≺ (x ∷ ys)

  record _∞≺_ (xs ys : ∞Colistˣ A) : Set where
    coinductive
    field
      force : force xs ≺ force ys

open _∞≺_

≺-refl : ∀ {xs : Colistˣ A} → xs ≺ xs
≺-refl {xs = []} = []
≺-refl {xs = fail} = fail
≺-refl {xs = x ∷ xs} = x ∷ λ where .force → ≺-refl

≺-trans : ∀ {xs ys zs : Colistˣ A}
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

≺-zip : ∀ {xs xs' : Colistˣ A} {ys ys' : Colistˣ B}
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

≺-unzipₗ : ∀ {xys' xys : Colistˣ (A × B)}
  → xys' ≺ xys
  → unzipₗ xys' ≺ unzipₗ xys
≺-unzipₗ [] = []
≺-unzipₗ fail = fail
≺-unzipₗ ((x , y) ∷ xys'≺xys) = x ∷ λ where .force → ≺-unzipₗ (force xys'≺xys)

≺-unzipᵣ : ∀ {xys' xys : Colistˣ (A × B)}
  → xys' ≺ xys
  → unzipᵣ xys' ≺ unzipᵣ xys
≺-unzipᵣ [] = []
≺-unzipᵣ fail = fail
≺-unzipᵣ ((x , y) ∷ xys'≺xys) = y ∷ λ where .force → ≺-unzipᵣ (force xys'≺xys)

≺-zip-unzip : ∀ (xys : Colistˣ (A × B))
  → zip (unzipₗ xys) (unzipᵣ xys) ≺ xys
≺-zip-unzip [] = []
≺-zip-unzip fail = fail
≺-zip-unzip (xy ∷ xys) = xy ∷ λ where .force → ≺-zip-unzip (force xys)

-------------------------------------------------------------------------------
-- Sequence transformation

ST : Set → Set → Set
ST X Y = Colistˣ X → Colistˣ Y

IsIncremental : ST X Y → Set
IsIncremental st = ∀ {xs xs'} → xs' ≺ xs → st xs' ≺ st xs

HasDelay : ℕ → ST X Y → Set
HasDelay d st = ∀ xs → colengthˣ (st xs) Coℕˣ≈ (colengthˣ xs ∸ℕ d)

record Is_-IST_ (d : ℕ) (st : ST X Y) : Set where
  field
    empty : st [] ≡ []
    isIncremental : IsIncremental st
    hasDelay : HasDelay d st

_IsIISTOf_ : ST X Y → ST Y X → Set
st' IsIISTOf st = ∀ xs → st' (st xs) ≺ xs

record _Is_-IISTOf_ (st' : ST X Y) (d : ℕ) (st : ST Y X) : Set where
  field
    is-d-IST : Is d -IST st'
    isIIST : st' IsIISTOf st

record Is⟨_,_⟩-IIST_ (d d' : ℕ) (st : ST X Y) : Set where
  field
    inverse : ST Y X
    is-d-IST : Is d -IST st
    inverse-is-d'-IIST : inverse Is d' -IISTOf st

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

I⟦_⟧ : E X Y → E Y X
I⟦ map-fold a f g ⟧ = map-fold a (inv⇌ ∘ f) (λ a → maybe (g a) a ∘ f a .from)
I⟦ delay x ⟧ = hasten x
I⟦ hasten x ⟧ = delay x
I⟦ e ⟫ e' ⟧ = I⟦ e' ⟧ ⟫ I⟦ e ⟧
I⟦ e ⊗ e' ⟧ = I⟦ e ⟧ ⊗ I⟦ e' ⟧

--------------------------------------------------------------------------------

F-empty : ∀ (e : E X Y) → F⟦ e ⟧ [] ≡ []
F-empty (map-fold a f g) = refl
F-empty (delay x) = refl
F-empty (hasten x) = refl
F-empty (e ⟫ e') rewrite F-empty e | F-empty e' = refl
F-empty (e ⊗ e') rewrite F-empty e | F-empty e' = refl

B-empty : ∀ (e : E X Y) → B⟦ e ⟧ [] ≡ []
B-empty (map-fold a f g) = refl
B-empty (delay x) = refl
B-empty (hasten x) = refl
B-empty (e ⟫ e') rewrite B-empty e' | B-empty e = refl
B-empty (e ⊗ e') rewrite B-empty e | B-empty e' = refl

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
F-delay (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → HasDelay 0 F⟦ map-fold a f g ⟧
    helper a [] = zero
    helper a fail = failL
    helper a (x ∷ xs) with f a .to x
    ... | nothing = failL
    ... | just y = suc λ where .force → helper (g a x) (force xs)
F-delay (delay x) [] = zero
F-delay (delay x) fail = failR
F-delay (delay x) (y ∷ xs) = suc λ where .force → F-delay (delay y) (force xs)
F-delay (hasten x) [] = zero
F-delay (hasten x) fail = failL
F-delay (hasten x) (y ∷ xs) with x ≟ y
... | no _ = failL
... | yes _ = Coℕˣ≈-refl
F-delay (e ⟫ e') xs =
  let ih = F-delay e xs
      ih' = F-delay e' (F⟦ e ⟧ xs)
   in {!   !}
F-delay (e ⊗ e') xzs =
  let ih = F-delay e (unzipₗ xzs)
      ih' = F-delay e' (unzipᵣ xzs)
   in {!   !}

B-delay : ∀ (e : E X Y) → HasDelay DB⟦ e ⟧ B⟦ e ⟧
B-delay (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → HasDelay 0 B⟦ map-fold a f g ⟧
    helper a [] = zero
    helper a fail = failL
    helper a (y ∷ ys) with f a .from y
    ... | nothing = failL
    ... | just x = suc λ where .force → helper (g a x) (force ys)
B-delay (delay x) [] = zero
B-delay (delay x) fail = failL
B-delay (delay x) (y ∷ xs) with x ≟ y
... | no _ = failL
... | yes _ = Coℕˣ≈-refl
B-delay (hasten x) [] = zero
B-delay (hasten x) fail = failR
B-delay (hasten x) (y ∷ xs) = suc λ where .force → B-delay (hasten y) (force xs)
B-delay (e ⟫ e') zs =
  let ih = B-delay e' zs
      ih' = B-delay e (B⟦ e' ⟧ zs)
   in {!   !}
B-delay (e ⊗ e') yws =
  let ih = B-delay e (unzipₗ yws)
      ih' = B-delay e' (unzipᵣ yws)
   in {!   !}

F-IIST : ∀ (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → F⟦ map-fold a f g ⟧ IsIISTOf B⟦ map-fold a f g ⟧
    helper a [] = []
    helper a fail = fail
    helper a (y ∷ ys) with f a .from y in eq
    ... | nothing = {!   !}
    ... | just x rewrite f a .invertible₂ eq =
          y ∷ λ where .force → helper (g a x) (force ys)
F-IIST (delay x) [] = []
F-IIST (delay x) fail = {!   !}
F-IIST (delay x) (y ∷ ys) with x ≟ y
... | no _ = {!   !}
... | yes refl = shift-≺-∷ y (force ys)
F-IIST (hasten x) [] = []
F-IIST (hasten x) fail with x ≟ x
... | no _ = fail
... | yes _ = fail
F-IIST (hasten x) (y ∷ ys) with x ≟ x
... | no contra with () ← contra refl
... | yes refl = shift-≺-∷ y (force ys)
F-IIST (e ⟫ e') zs =
  let ih = F-IIST e (B⟦ e' ⟧ zs)
      ih' = F-IIST e' zs
   in ≺-trans (F-incremental e' ih) ih'
F-IIST (e ⊗ e') yws =
  let ih = F-IIST e (unzipₗ yws)
      ih' = F-IIST e' (unzipᵣ yws)
   in {!   !}

B-IIST : ∀ (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → B⟦ map-fold a f g ⟧ IsIISTOf F⟦ map-fold a f g ⟧
    helper a [] = []
    helper a fail = fail
    helper a (x ∷ xs) with f a .to x in eq
    ... | nothing = {!   !}
    ... | just y rewrite f a .invertible₁ eq =
          x ∷ λ where .force → helper (g a x) (force xs)
B-IIST (delay x) [] = []
B-IIST (delay x) fail with x ≟ x
... | no _ = fail
... | yes _ = fail
B-IIST (delay x) (y ∷ ys) with x ≟ x
... | no contra with () ← contra refl
... | yes refl = shift-≺-∷ y (force ys)
B-IIST (hasten x) [] = []
B-IIST (hasten x) fail = {!   !}
B-IIST (hasten x) (y ∷ ys) with x ≟ y
... | no _ = {!   !}
... | yes refl = shift-≺-∷ y (force ys)
B-IIST (e ⟫ e') zs =
  let ih = B-IIST e' (F⟦ e ⟧ zs)
      ih' = B-IIST e zs
   in ≺-trans (B-incremental e ih) ih'
B-IIST (e ⊗ e') yws =
  let ih = B-IIST e (unzipₗ yws)
      ih' = B-IIST e' (unzipᵣ yws)
   in {!   !}

F-d-IST : ∀ (e : E X Y) → Is DF⟦ e ⟧ -IST F⟦ e ⟧
F-d-IST e = record
  { empty = F-empty e
  ; isIncremental = F-incremental e
  ; hasDelay = F-delay e
  }

B-d-IST : ∀ (e : E X Y) → Is DB⟦ e ⟧ -IST B⟦ e ⟧
B-d-IST e = record
  { empty = B-empty e
  ; isIncremental = B-incremental e
  ; hasDelay = B-delay e
  }

F-d-IIST : ∀ (e : E X Y) → F⟦ e ⟧ Is DF⟦ e ⟧ -IISTOf B⟦ e ⟧
F-d-IIST e = record { is-d-IST = F-d-IST e; isIIST = F-IIST e }

B-d-IIST : ∀ (e : E X Y) → B⟦ e ⟧ Is DB⟦ e ⟧ -IISTOf F⟦ e ⟧
B-d-IIST e = record { is-d-IST = B-d-IST e; isIIST = B-IIST e }

F-d-d'-IIST : ∀ (e : E X Y) → Is⟨ DF⟦ e ⟧ , DB⟦ e ⟧ ⟩-IIST F⟦ e ⟧
F-d-d'-IIST e = record
  { inverse = B⟦ e ⟧
  ; is-d-IST = F-d-IST e
  ; inverse-is-d'-IIST = B-d-IIST e
  }

B-d-d'-IIST : ∀ (e : E X Y) → Is⟨ DB⟦ e ⟧ , DF⟦ e ⟧ ⟩-IIST B⟦ e ⟧
B-d-d'-IIST e = record
  { inverse = F⟦ e ⟧
  ; is-d-IST = B-d-IST e
  ; inverse-is-d'-IIST = F-d-IIST e
  }

F∘I≡B : ∀ (e : E X Y) (ys : Colistˣ Y)
  → F⟦ I⟦ e ⟧ ⟧ ys Colistˣ≈ B⟦ e ⟧ ys
F∘I≡B {Y = Y} (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) (ys : Colistˣ Y)
      → F⟦ I⟦ map-fold a f g ⟧ ⟧ ys Colistˣ≈ B⟦ map-fold a f g ⟧ ys
    helper a [] = []
    helper a fail = fail
    helper a (y ∷ ys) with f a .from y in eq
    ... | nothing = fail
    ... | just x rewrite f a .invertible₂ eq = {!   !}
F∘I≡B (delay x) ys = Colistˣ≈-refl
F∘I≡B (hasten x) ys = Colistˣ≈-refl
F∘I≡B (e ⟫ e') ys =
  let ih = F∘I≡B e' ys
   in {!   !}
F∘I≡B (e ⊗ e') yws =
  let ih = F∘I≡B e (unzipₗ yws)
      ih' = F∘I≡B e' (unzipᵣ yws)
   in Colistˣ≈-zip ih ih'

B∘I≡F : ∀ (e : E X Y) (xs : Colistˣ X)
  → B⟦ I⟦ e ⟧ ⟧ xs Colistˣ≈ F⟦ e ⟧ xs
B∘I≡F {X = X} (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) (xs : Colistˣ X)
      → B⟦ I⟦ map-fold a f g ⟧ ⟧ xs Colistˣ≈ F⟦ map-fold a f g ⟧ xs
    helper a [] = []
    helper a fail = fail
    helper a (x ∷ xs) with f a .to x in eq
    ... | nothing = fail
    ... | just y rewrite f a .invertible₁ eq = {!   !}
B∘I≡F (delay x) xs = Colistˣ≈-refl
B∘I≡F (hasten x) xs = Colistˣ≈-refl
B∘I≡F (e ⟫ e') xs =
  let ih = B∘I≡F e xs
   in {!   !}
B∘I≡F (e ⊗ e') xzs =
  let ih = B∘I≡F e (unzipₗ xzs)
      ih' = B∘I≡F e' (unzipᵣ xzs)
   in Colistˣ≈-zip ih ih'
