{-# OPTIONS --guardedness #-}

module IIST-inf where

open import Data.Maybe.Base using ( Maybe; just; nothing; maybe )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Nat.Properties using ( +-identityʳ; +-comm )
open import Data.Product.Base as Prod using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Unit.Base using ( ⊤; tt )
open import Function using ( _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; _≢_; refl; sym; trans; cong )
open import Relation.Nullary using ( ¬_; yes; no )

open import Codata.FallibleColist as Colistˣ
open import Codata.FallibleConat as Coℕˣ
open import IIST.Common
open import IIST.Syntax

private
  variable
    A B X Y Z W : Set

-------------------------------------------------------------------------------
-- Fallible Colist

shift : A → Colistˣ A → Colistˣ A
shift x [] = []
shift x fail = fail
shift x (y ∷ xs) = x ∷ λ where .force → shift y (force xs)

unshift : {{_ : Eq A}} → A → Colistˣ A → Colistˣ A
unshift x [] = []
unshift x fail = fail
unshift x (y ∷ xs) with x ≟ y
... | no _ = fail
... | yes _ = force xs

-------------------------------------------------------------------------------
-- Prefix

shift-≺-∷ : ∀ (x : A) xs → (shift x xs) Colistˣ.≺ (x ∷ delay xs)
shift-≺-∷ x [] = []
shift-≺-∷ x fail = fail
shift-≺-∷ x (y ∷ xs) = x ∷ λ where .force → shift-≺-∷ y (force xs)

≺-shift : ∀ (x : A) {xs ys} → xs Colistˣ.≺ ys → shift x xs Colistˣ.≺ shift x ys
≺-shift x [] = []
≺-shift x fail = fail
≺-shift x (y ∷ xs≺ys) = x ∷ λ where .force → ≺-shift y (force xs≺ys)

≺-unshift : ∀ {{_ : Eq A}} (x : A) {xs ys} → xs Colistˣ.≺ ys → unshift x xs Colistˣ.≺ unshift x ys
≺-unshift x [] = []
≺-unshift x fail = fail
≺-unshift x (y ∷ xs≺ys) with x ≟ y
... | no _ = fail
... | yes _ = force xs≺ys

-------------------------------------------------------------------------------
-- Sequence transformation

ST : Set → Set → Set
ST X Y = Colistˣ X → Colistˣ Y

IsIncremental : ST X Y → Set
IsIncremental st = ∀ {xs xs'} → xs' Colistˣ.≺ xs → st xs' Colistˣ.≺ st xs

HasDelay : ℕ → ST X Y → Set
HasDelay d st = ∀ xs → colength (st xs) Coℕˣ.≺ (colength xs ∸ℕ d)

record Is_-IST_ (d : ℕ) (st : ST X Y) : Set where
  field
    empty : st [] ≡ []
    isIncremental : IsIncremental st
    hasDelay : HasDelay d st

_IsIISTOf_ : ST X Y → ST Y X → Set
st' IsIISTOf st = ∀ xs → st' (st xs) Colistˣ.≺ xs

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

--------------------------------------------------------------------------------
-- Incrementality of F⟦_⟧ and B⟦_⟧

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

--------------------------------------------------------------------------------
-- d-Incrementality of F⟦_⟧ and B⟦_⟧

shift-colength : ∀ (x : A) xs → colength (shift x xs) Coℕˣ.≺ colength xs
shift-colength x [] = ≺zero
shift-colength x fail = ≺fail
shift-colength x (y ∷ xs) = ≺suc λ where .force → shift-colength y (force xs)

unshift-colength : ∀ {{_ : Eq A}} (x : A) xs → colength (unshift x xs) Coℕˣ.≺ (colength xs ∸ℕ 1)
unshift-colength x [] = ≺zero
unshift-colength x fail = ≺fail
unshift-colength x (y ∷ xs) with x ≟ y
... | no _ = ≺fail
... | yes _ = Coℕˣ.≺-refl

F-delay : ∀ (e : E X Y) → HasDelay DF⟦ e ⟧ F⟦ e ⟧
F-delay (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → HasDelay 0 F⟦ map-fold a f g ⟧
    helper a [] = ≺zero
    helper a fail = ≺fail
    helper a (x ∷ xs) with f a .to x
    ... | nothing = ≺fail
    ... | just y = ≺suc λ where .force → helper (g a x) (force xs)
F-delay (delay x) = shift-colength x
F-delay (hasten x) = unshift-colength x
F-delay (e ⟫ e') xs =
  let ih = F-delay e xs
      ih' = F-delay e' (F⟦ e ⟧ xs)
   in Coℕˣ.≺-trans
        ih'
        (Coℕˣ.≺-trans
          (≺-∸ℕ DF⟦ e' ⟧ ih)
          (≈-to-≺ (∸-+-assoc (colength xs) DF⟦ e ⟧ DF⟦  e' ⟧)))
F-delay (e ⊗ e') xzs =
  let ih = F-delay e (unzipₗ xzs)
      ih' = F-delay e' (unzipᵣ xzs)
   in Coℕˣ.≺-trans
        (Coℕˣ.≺-trans
          (≈-to-≺ colength-zip)
          (≺-⊓
            (Coℕˣ.≺-trans ih (≺-∸ℕ DF⟦ e ⟧ (≈-to-≺ colength-unzipₗ)))
            (Coℕˣ.≺-trans ih' (≺-∸ℕ DF⟦ e' ⟧ (≈-to-≺ colength-unzipᵣ)))))
        (≈-to-≺ (Coℕˣ.≈-sym (∸ℕ-distribˡ-⊔-⊓ (colength xzs) DF⟦ e ⟧ DF⟦ e' ⟧)))

B-delay : ∀ (e : E X Y) → HasDelay DB⟦ e ⟧ B⟦ e ⟧
B-delay (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → HasDelay 0 B⟦ map-fold a f g ⟧
    helper a [] = ≺zero
    helper a fail = ≺fail
    helper a (y ∷ ys) with f a .from y
    ... | nothing = ≺fail
    ... | just x = ≺suc λ where .force → helper (g a x) (force ys)
B-delay (delay x) = unshift-colength x
B-delay (hasten x) = shift-colength x
B-delay (e ⟫ e') zs rewrite +-comm DB⟦ e ⟧ DB⟦ e' ⟧ =
  let ih = B-delay e' zs
      ih' = B-delay e (B⟦ e' ⟧ zs)
   in Coℕˣ.≺-trans
        ih'
        (Coℕˣ.≺-trans
          (≺-∸ℕ DB⟦ e ⟧ ih)
          (≈-to-≺ (∸-+-assoc (colength zs) DB⟦ e' ⟧ DB⟦  e ⟧)))
B-delay (e ⊗ e') yws =
  let ih = B-delay e (unzipₗ yws)
      ih' = B-delay e' (unzipᵣ yws)
   in Coℕˣ.≺-trans
        (Coℕˣ.≺-trans
          (≈-to-≺ colength-zip)
          (≺-⊓
            (Coℕˣ.≺-trans ih (≺-∸ℕ DB⟦ e ⟧ (≈-to-≺ colength-unzipₗ)))
            (Coℕˣ.≺-trans ih' (≺-∸ℕ DB⟦ e' ⟧ (≈-to-≺ colength-unzipᵣ)))))
        (≈-to-≺ (Coℕˣ.≈-sym (∸ℕ-distribˡ-⊔-⊓ (colength yws) DB⟦ e ⟧ DB⟦ e' ⟧)))

--------------------------------------------------------------------------------
-- F⟦_⟧ and B⟦_⟧ are inverse of each other

F-IIST : ∀ (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → F⟦ map-fold a f g ⟧ IsIISTOf B⟦ map-fold a f g ⟧
    helper a [] = []
    helper a fail = fail
    helper a (y ∷ ys) with f a .from y in eq
    ... | nothing = fail
    ... | just x rewrite f a .from→to eq =
          y ∷ λ where .force → helper (g a x) (force ys)
F-IIST (delay x) [] = []
F-IIST (delay x) fail = fail
F-IIST (delay x) (y ∷ ys) with x ≟ y
... | no _ = fail
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
   in Colistˣ.≺-trans (F-incremental e' ih) ih'
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
    ... | nothing = fail
    ... | just y rewrite f a .to→from eq =
          x ∷ λ where .force → helper (g a x) (force xs)
B-IIST (delay x) [] = []
B-IIST (delay x) fail with x ≟ x
... | no _ = fail
... | yes _ = fail
B-IIST (delay x) (y ∷ ys) with x ≟ x
... | no contra with () ← contra refl
... | yes refl = shift-≺-∷ y (force ys)
B-IIST (hasten x) [] = []
B-IIST (hasten x) fail = fail
B-IIST (hasten x) (y ∷ ys) with x ≟ y
... | no _ = fail
... | yes refl = shift-≺-∷ y (force ys)
B-IIST (e ⟫ e') zs =
  let ih = B-IIST e' (F⟦ e ⟧ zs)
      ih' = B-IIST e zs
   in Colistˣ.≺-trans (B-incremental e ih) ih'
B-IIST (e ⊗ e') yws =
  let ih = B-IIST e (unzipₗ yws)
      ih' = B-IIST e' (unzipᵣ yws)
   in {!   !}

--------------------------------------------------------------------------------
-- Bundles

-- F-d-IST : ∀ (e : E X Y) → Is DF⟦ e ⟧ -IST F⟦ e ⟧
-- F-d-IST e = record
--   { empty = F-empty e
--   ; isIncremental = F-incremental e
--   ; hasDelay = F-delay e
--   }

-- B-d-IST : ∀ (e : E X Y) → Is DB⟦ e ⟧ -IST B⟦ e ⟧
-- B-d-IST e = record
--   { empty = B-empty e
--   ; isIncremental = B-incremental e
--   ; hasDelay = B-delay e
--   }

-- F-d-IIST : ∀ (e : E X Y) → F⟦ e ⟧ Is DF⟦ e ⟧ -IISTOf B⟦ e ⟧
-- F-d-IIST e = record { is-d-IST = F-d-IST e; isIIST = F-IIST e }

-- B-d-IIST : ∀ (e : E X Y) → B⟦ e ⟧ Is DB⟦ e ⟧ -IISTOf F⟦ e ⟧
-- B-d-IIST e = record { is-d-IST = B-d-IST e; isIIST = B-IIST e }

-- F-d-d'-IIST : ∀ (e : E X Y) → Is⟨ DF⟦ e ⟧ , DB⟦ e ⟧ ⟩-IIST F⟦ e ⟧
-- F-d-d'-IIST e = record
--   { inverse = B⟦ e ⟧
--   ; is-d-IST = F-d-IST e
--   ; inverse-is-d'-IIST = B-d-IIST e
--   }

-- B-d-d'-IIST : ∀ (e : E X Y) → Is⟨ DB⟦ e ⟧ , DF⟦ e ⟧ ⟩-IIST B⟦ e ⟧
-- B-d-d'-IIST e = record
--   { inverse = F⟦ e ⟧
--   ; is-d-IST = B-d-IST e
--   ; inverse-is-d'-IIST = F-d-IIST e
--   }

--------------------------------------------------------------------------------
-- Properties of I⟦_⟧

≈-shift : ∀ (x : A) {xs ys} → xs Colistˣ.≈ ys → shift x xs Colistˣ.≈ shift x ys
≈-shift x ≈[] = ≈[]
≈-shift x ≈fail = ≈fail
≈-shift x (refl ≈∷ xs≈ys) = refl ≈∷ λ where .force → ≈-shift _ (force xs≈ys)

≈-unshift : ∀ {{_ : Eq A}} (x : A) {xs ys} → xs Colistˣ.≈ ys → unshift x xs Colistˣ.≈ unshift x ys
≈-unshift x ≈[] = ≈[]
≈-unshift x ≈fail = ≈fail
≈-unshift x (_≈∷_ {y = y} refl xs≈ys) with x ≟ y
... | no _ = ≈fail
... | yes _ = force xs≈ys

F-≈ : ∀ (e : E X Y) {xs ys : Colistˣ X}
  → xs Colistˣ.≈ ys
  → F⟦ e ⟧ xs Colistˣ.≈ F⟦ e ⟧ ys
F-≈ {X = X} (map-fold {A} a f g) = helper a
  where
    helper : (a : A) {xs ys : Colistˣ X}
      → xs Colistˣ.≈ ys
      → F⟦ map-fold a f g ⟧ xs Colistˣ.≈ F⟦ map-fold a f g ⟧ ys
    helper a ≈[] = ≈[]
    helper a ≈fail = ≈fail
    helper a (_≈∷_ {x = x} refl xs≈ys) with f a .to x
    ... | nothing = ≈fail
    ... | just y = refl ≈∷ λ where .force → helper (g a x) (force xs≈ys)
F-≈ (delay x) = ≈-shift x
F-≈ (hasten x) = ≈-unshift x
F-≈ (e ⟫ e') = F-≈ e' ∘ F-≈ e
F-≈ (e ⊗ e') xs≈ys = ≈-zip (F-≈ e (≈-unzipₗ xs≈ys)) (F-≈ e' (≈-unzipᵣ xs≈ys))

B-≈ : ∀ (e : E X Y) {xs ys : Colistˣ Y}
  → xs Colistˣ.≈ ys
  → B⟦ e ⟧ xs Colistˣ.≈ B⟦ e ⟧ ys
B-≈ {Y = Y} (map-fold {A} a f g) = helper a
  where
    helper : (a : A) {xs ys : Colistˣ Y}
      → xs Colistˣ.≈ ys
      → B⟦ map-fold a f g ⟧ xs Colistˣ.≈ B⟦ map-fold a f g ⟧ ys
    helper a ≈[] = ≈[]
    helper a ≈fail = ≈fail
    helper a (_≈∷_ {x = y} refl xs≈ys) with f a .from y
    ... | nothing = ≈fail
    ... | just x = refl ≈∷ λ where .force → helper (g a x) (force xs≈ys)
B-≈ (delay x) = ≈-unshift x
B-≈ (hasten x) = ≈-shift x
B-≈ (e ⟫ e') = B-≈ e ∘ B-≈ e'
B-≈ (e ⊗ e') xs≈ys = ≈-zip (B-≈ e (≈-unzipₗ xs≈ys)) (B-≈ e' (≈-unzipᵣ xs≈ys))

F∘I≡B : ∀ (e : E X Y) (ys : Colistˣ Y)
  → F⟦ I⟦ e ⟧ ⟧ ys Colistˣ.≈ B⟦ e ⟧ ys
F∘I≡B {Y = Y} (map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → (ys : Colistˣ Y)
      → F⟦ I⟦ map-fold a f g ⟧ ⟧ ys Colistˣ.≈ B⟦ map-fold a' f g ⟧ ys
    helper _ [] = ≈[]
    helper _ fail = ≈fail
    helper {a} refl (y ∷ ys) with f a .from y in eq
    ... | nothing = ≈fail
    ... | just x =
          refl ≈∷ λ where .force → helper (cong (maybe (g a) a) eq) (force ys)
F∘I≡B (delay x) ys = Colistˣ.≈-refl
F∘I≡B (hasten x) ys = Colistˣ.≈-refl
F∘I≡B (e ⟫ e') ys =
  let ih = F∘I≡B e' ys
      ih' = F∘I≡B e (F⟦ I⟦ e' ⟧ ⟧ ys)
   in Colistˣ.≈-trans ih' (B-≈ e ih)
F∘I≡B (e ⊗ e') yws =
  let ih = F∘I≡B e (unzipₗ yws)
      ih' = F∘I≡B e' (unzipᵣ yws)
   in ≈-zip ih ih'

B∘I≡F : ∀ (e : E X Y) (xs : Colistˣ X)
  → B⟦ I⟦ e ⟧ ⟧ xs Colistˣ.≈ F⟦ e ⟧ xs
B∘I≡F {X = X} (map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → (xs : Colistˣ X)
      → B⟦ I⟦ map-fold a f g ⟧ ⟧ xs Colistˣ.≈ F⟦ map-fold a' f g ⟧ xs
    helper _ [] = ≈[]
    helper _ fail = ≈fail
    helper {a} refl (x ∷ xs) with f a .to x in eq
    ... | nothing = ≈fail
    ... | just y =
          refl ≈∷ λ where
            .force → helper (cong (maybe (g a) a) (f a .to→from eq)) (force xs)
B∘I≡F (delay x) xs = Colistˣ.≈-refl
B∘I≡F (hasten x) xs = Colistˣ.≈-refl
B∘I≡F (e ⟫ e') xs =
  let ih = B∘I≡F e xs
      ih' = B∘I≡F e' (B⟦ I⟦ e ⟧ ⟧ xs)
   in Colistˣ.≈-trans ih' (F-≈ e' ih)
B∘I≡F (e ⊗ e') xzs =
  let ih = B∘I≡F e (unzipₗ xzs)
      ih' = B∘I≡F e' (unzipᵣ xzs)
   in ≈-zip ih ih'
