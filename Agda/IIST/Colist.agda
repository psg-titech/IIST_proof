{-# OPTIONS --guardedness #-}

module IIST.Colist where

open import Data.Maybe.Base using ( Maybe; just; nothing; maybe )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Nat.Properties using ( +-identityʳ; +-comm )
open import Data.Product.Base as Prod using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Unit.Base using ( ⊤; tt )
open import Function using ( _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; _≢_; refl; sym; trans; cong )
open import Relation.Nullary using ( ¬_; yes; no )

open import Codata.PartialColist as Colist⊥
open import Codata.PartialConat as Coℕ⊥
open import IIST.Common
open import IIST.Syntax

private
  variable
    A B X Y Z W : Set

-------------------------------------------------------------------------------
-- Sequence transformation

ST : Set → Set → Set
ST X Y = Colist⊥ X → Colist⊥ Y

IsIncremental : ST X Y → Set
IsIncremental st = ∀ {xs xs'} → xs' Colist⊥.≺ xs → st xs' Colist⊥.≺ st xs

HasDelay : ℕ → ST X Y → Set
HasDelay d st = ∀ xs → colength (st xs) Coℕ⊥.⊑ (colength xs ∸ℕ d)

record Is_-IST_ (d : ℕ) (st : ST X Y) : Set where
  field
    empty : st [] ≡ []
    isIncremental : IsIncremental st
    hasDelay : HasDelay d st

_IsIISTOf_ : ST X Y → ST Y X → Set
st' IsIISTOf st = ∀ xs → st' (st xs) Colist⊥.≺ xs

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
-- IIST constructors and their semantics

shift : A → Colist⊥ A → Colist⊥ A
shift x [] = []
shift x ⊥ = ⊥
shift x (y ∷ xs) = x ∷ λ where .force → shift y (force xs)

unshift : {{_ : Eq A}} → A → Colist⊥ A → Colist⊥ A
unshift x [] = []
unshift x ⊥ = ⊥
unshift x (y ∷ xs) with x ≟ y
... | no _ = ⊥
... | yes _ = force xs

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST X Y
F-map-fold a f g [] = []
F-map-fold a f g ⊥ = ⊥
F-map-fold a f g (x ∷ xs) with f a .to x
... | nothing = ⊥
... | just y = y ∷ λ where .force → F-map-fold (g a x) f g (force xs)

F⟦_⟧ : E X Y → ST X Y
F⟦ `map-fold a f g ⟧ = F-map-fold a f g
F⟦ `delay x ⟧ = shift x
F⟦ `hasten x ⟧ = unshift x
F⟦ e `⋙ e' ⟧ = F⟦ e' ⟧ ∘ F⟦ e ⟧
F⟦ e `⊗ e' ⟧ xzs = zip (F⟦ e ⟧ (unzipₗ xzs)) (F⟦ e' ⟧ (unzipᵣ xzs))

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST Y X
B-map-fold a f g [] = []
B-map-fold a f g ⊥ = ⊥
B-map-fold a f g (y ∷ ys) with f a .from y
... | nothing = ⊥
... | just x = x ∷ λ where .force → B-map-fold (g a x) f g (force ys)

B⟦_⟧ : E X Y → ST Y X
B⟦ `map-fold a f g ⟧ = B-map-fold a f g
B⟦ `delay x ⟧ = unshift x
B⟦ `hasten x ⟧ = shift x
B⟦ e `⋙ e' ⟧ = B⟦ e ⟧ ∘ B⟦ e' ⟧
B⟦ e `⊗ e' ⟧ xzs = zip (B⟦ e ⟧ (unzipₗ xzs)) (B⟦ e' ⟧ (unzipᵣ xzs))

--------------------------------------------------------------------------------

F-empty : ∀ (e : E X Y) → F⟦ e ⟧ [] ≡ []
F-empty (`map-fold a f g) = refl
F-empty (`delay x) = refl
F-empty (`hasten x) = refl
F-empty (e `⋙ e') rewrite F-empty e | F-empty e' = refl
F-empty (e `⊗ e') rewrite F-empty e | F-empty e' = refl

B-empty : ∀ (e : E X Y) → B⟦ e ⟧ [] ≡ []
B-empty (`map-fold a f g) = refl
B-empty (`delay x) = refl
B-empty (`hasten x) = refl
B-empty (e `⋙ e') rewrite B-empty e' | B-empty e = refl
B-empty (e `⊗ e') rewrite B-empty e | B-empty e' = refl

--------------------------------------------------------------------------------
-- Incrementality of F and B

shift-≺-∷ : ∀ (x : A) xs → shift x xs Colist⊥.≺ x ∷ delay xs
shift-≺-∷ x [] = []
shift-≺-∷ x ⊥ = ⊥
shift-≺-∷ x (y ∷ xs) = x ∷ λ where .force → shift-≺-∷ y (force xs)

≺-cong-shift : ∀ (x : A) {xs ys} → xs Colist⊥.≺ ys → shift x xs Colist⊥.≺ shift x ys
≺-cong-shift x [] = []
≺-cong-shift x ⊥ = ⊥
≺-cong-shift x (y ∷ p) = x ∷ λ where .force → ≺-cong-shift y (force p)

≺-cong-unshift : ∀ {{_ : Eq A}} (x : A) {xs ys} → xs Colist⊥.≺ ys → unshift x xs Colist⊥.≺ unshift x ys
≺-cong-unshift x [] = []
≺-cong-unshift x ⊥ = ⊥
≺-cong-unshift x (y ∷ p) with x ≟ y
... | no _ = ⊥
... | yes _ = force p

F-incremental : ∀ (e : E X Y) → IsIncremental F⟦ e ⟧
F-incremental (`map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → IsIncremental F⟦ `map-fold a f g ⟧
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (x ∷ p) with f a .to x
    ... | nothing = ⊥
    ... | just y = y ∷ λ where .force → helper (g a x) (force p)
F-incremental (`delay x) = ≺-cong-shift x
F-incremental (`hasten x) = ≺-cong-unshift x
F-incremental (e `⋙ e') = F-incremental e' ∘ F-incremental e
F-incremental (e `⊗ e') p =
  ≺-cong-zip (F-incremental e (≺-cong-unzipₗ p)) (F-incremental e' (≺-cong-unzipᵣ p))

B-incremental : ∀ (e : E X Y) → IsIncremental B⟦ e ⟧
B-incremental (`map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → IsIncremental B⟦ `map-fold a f g ⟧
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (y ∷ p) with f a .from y
    ... | nothing = ⊥
    ... | just x = x ∷ λ where .force → helper (g a x) (force p)
B-incremental (`delay x) = ≺-cong-unshift x
B-incremental (`hasten x) = ≺-cong-shift x
B-incremental (e `⋙ e') = B-incremental e ∘ B-incremental e'
B-incremental (e `⊗ e') yws'≺yws =
  ≺-cong-zip (B-incremental e (≺-cong-unzipₗ yws'≺yws)) (B-incremental e' (≺-cong-unzipᵣ yws'≺yws))

--------------------------------------------------------------------------------
-- d-Incrementality of F and B

shift-colength : ∀ (x : A) xs → colength (shift x xs) Coℕ⊥.⊑ colength xs
shift-colength x [] = zero
shift-colength x ⊥ = ⊥ₗ
shift-colength x (y ∷ xs) = suc λ where .force → shift-colength y (force xs)

unshift-colength : ∀ {{_ : Eq A}} (x : A) xs → colength (unshift x xs) Coℕ⊥.⊑ (colength xs ∸ℕ 1)
unshift-colength x [] = zero
unshift-colength x ⊥ = ⊥ₗ
unshift-colength x (y ∷ xs) with x ≟ y
... | no _ = ⊥ₗ
... | yes _ = Coℕ⊥.⊑-refl

F-hasDelay : ∀ (e : E X Y) → HasDelay DF⟦ e ⟧ F⟦ e ⟧
F-hasDelay (`map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → HasDelay 0 F⟦ `map-fold a f g ⟧
    helper a [] = zero
    helper a ⊥ = ⊥ₗ
    helper a (x ∷ xs) with f a .to x
    ... | nothing = ⊥ₗ
    ... | just y = suc λ where .force → helper (g a x) (force xs)
F-hasDelay (`delay x) = shift-colength x
F-hasDelay (`hasten x) = unshift-colength x
F-hasDelay (e `⋙ e') xs =
  let ih = F-hasDelay e xs
      ih' = F-hasDelay e' (F⟦ e ⟧ xs)
   in Coℕ⊥.⊑-trans
        ih'
        (Coℕ⊥.⊑-trans
          (⊑-cong-∸ℕ DF⟦ e' ⟧ ih)
          (≈-to-⊑ (∸ℕ-+-assoc (colength xs) DF⟦ e ⟧ DF⟦  e' ⟧)))
F-hasDelay (e `⊗ e') xzs =
  let ih = F-hasDelay e (unzipₗ xzs)
      ih' = F-hasDelay e' (unzipᵣ xzs)
   in Coℕ⊥.⊑-trans
        (Coℕ⊥.⊑-trans
          (≈-to-⊑ colength-zip)
          (⊑-cong-⊓
            (Coℕ⊥.⊑-trans ih (⊑-cong-∸ℕ DF⟦ e ⟧ (≈-to-⊑ colength-unzipₗ)))
            (Coℕ⊥.⊑-trans ih' (⊑-cong-∸ℕ DF⟦ e' ⟧ (≈-to-⊑ colength-unzipᵣ)))))
        (≈-to-⊑ (Coℕ⊥.≈-sym (∸ℕ-distribˡ-⊔-⊓ (colength xzs) DF⟦ e ⟧ DF⟦ e' ⟧)))

B-hasDelay : ∀ (e : E X Y) → HasDelay DB⟦ e ⟧ B⟦ e ⟧
B-hasDelay (`map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → HasDelay 0 B⟦ `map-fold a f g ⟧
    helper a [] = zero
    helper a ⊥ = ⊥ₗ
    helper a (y ∷ ys) with f a .from y
    ... | nothing = ⊥ₗ
    ... | just x = suc λ where .force → helper (g a x) (force ys)
B-hasDelay (`delay x) = unshift-colength x
B-hasDelay (`hasten x) = shift-colength x
B-hasDelay (e `⋙ e') zs rewrite +-comm DB⟦ e ⟧ DB⟦ e' ⟧ =
  let ih = B-hasDelay e' zs
      ih' = B-hasDelay e (B⟦ e' ⟧ zs)
   in Coℕ⊥.⊑-trans
        ih'
        (Coℕ⊥.⊑-trans
          (⊑-cong-∸ℕ DB⟦ e ⟧ ih)
          (≈-to-⊑ (∸ℕ-+-assoc (colength zs) DB⟦ e' ⟧ DB⟦  e ⟧)))
B-hasDelay (e `⊗ e') yws =
  let ih = B-hasDelay e (unzipₗ yws)
      ih' = B-hasDelay e' (unzipᵣ yws)
   in Coℕ⊥.⊑-trans
        (Coℕ⊥.⊑-trans
          (≈-to-⊑ colength-zip)
          (⊑-cong-⊓
            (Coℕ⊥.⊑-trans ih (⊑-cong-∸ℕ DB⟦ e ⟧ (≈-to-⊑ colength-unzipₗ)))
            (Coℕ⊥.⊑-trans ih' (⊑-cong-∸ℕ DB⟦ e' ⟧ (≈-to-⊑ colength-unzipᵣ)))))
        (≈-to-⊑ (Coℕ⊥.≈-sym (∸ℕ-distribˡ-⊔-⊓ (colength yws) DB⟦ e ⟧ DB⟦ e' ⟧)))

--------------------------------------------------------------------------------
-- F⟦_⟧ and B⟦_⟧ are inverse of each other

shift-IIST : ∀ {{_ : Eq X}} (x : X) → shift x IsIISTOf unshift x
shift-IIST x [] = []
shift-IIST x ⊥ = ⊥
shift-IIST x (y ∷ xs) with x ≟ y
... | no _ = ⊥
... | yes refl = shift-≺-∷ x (force xs)

unshift-IIST : ∀ {{_ : Eq X}} (x : X) → unshift x IsIISTOf shift x
unshift-IIST x [] = []
unshift-IIST x ⊥ = ⊥
unshift-IIST x (y ∷ xs) with x ≟ x
... | no ¬refl with () ← ¬refl refl
... | yes refl = shift-≺-∷ y (force xs)

≺-cong-F : ∀ (e : E X Y) {xs ys : Colist⊥ X}
  → xs Colist⊥.≺ ys
  → F⟦ e ⟧ xs Colist⊥.≺ F⟦ e ⟧ ys
≺-cong-F {X = X} (`map-fold {A} a f g) = helper a
  where
    helper : (a : A) {xs ys : Colist⊥ X}
      → xs Colist⊥.≺ ys
      → F⟦ `map-fold a f g ⟧ xs Colist⊥.≺ F⟦ `map-fold a f g ⟧ ys
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (x ∷ p) with f a .to x
    ... | nothing = ⊥
    ... | just y = y ∷ λ where .force → helper (g a x) (force p)
≺-cong-F (`delay x) = ≺-cong-shift x
≺-cong-F (`hasten x) = ≺-cong-unshift x
≺-cong-F (e `⋙ e') = ≺-cong-F e' ∘ ≺-cong-F e
≺-cong-F (e `⊗ e') xs≺ys = ≺-cong-zip (≺-cong-F e (≺-cong-unzipₗ xs≺ys)) (≺-cong-F e' (≺-cong-unzipᵣ xs≺ys))

≺-cong-B : ∀ (e : E X Y) {xs ys : Colist⊥ Y}
  → xs Colist⊥.≺ ys
  → B⟦ e ⟧ xs Colist⊥.≺ B⟦ e ⟧ ys
≺-cong-B {Y = Y} (`map-fold {A} a f g) = helper a
  where
    helper : (a : A) {xs ys : Colist⊥ Y}
      → xs Colist⊥.≺ ys
      → B⟦ `map-fold a f g ⟧ xs Colist⊥.≺ B⟦ `map-fold a f g ⟧ ys
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (y ∷ p) with f a .from y
    ... | nothing = ⊥
    ... | just x = x ∷ λ where .force → helper (g a x) (force p)
≺-cong-B (`delay x) = ≺-cong-unshift x
≺-cong-B (`hasten x) = ≺-cong-shift x
≺-cong-B (e `⋙ e') = ≺-cong-B e ∘ ≺-cong-B e'
≺-cong-B (e `⊗ e') xs≺ys = ≺-cong-zip (≺-cong-B e (≺-cong-unzipₗ xs≺ys)) (≺-cong-B e' (≺-cong-unzipᵣ xs≺ys))

F-IIST : ∀ (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (`map-fold {A} a f g) = helper a
  where
    helper : (a : A) → F⟦ `map-fold a f g ⟧ IsIISTOf B⟦ `map-fold a f g ⟧
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (y ∷ ys) with f a .from y in eq
    ... | nothing = ⊥
    ... | just x rewrite f a .from→to eq =
          y ∷ λ where .force → helper (g a x) (force ys)
F-IIST (`delay x) = shift-IIST x
F-IIST (`hasten x) = unshift-IIST x
F-IIST (e `⋙ e') zs =
  let ih = F-IIST e (B⟦ e' ⟧ zs)
      ih' = F-IIST e' zs
   in Colist⊥.≺-trans (F-incremental e' ih) ih'
F-IIST (e `⊗ e') yws =
  let h1 = ≺-cong-F e (zip-unzipₗ (B⟦ e ⟧ (unzipₗ yws)) (B⟦ e' ⟧ (unzipᵣ yws)))
      h2 = ≺-cong-F e' (zip-unzipᵣ (B⟦ e ⟧ (unzipₗ yws)) (B⟦ e' ⟧ (unzipᵣ yws)))
      h3 = ≺-cong-zip h1 h2
      ih1 = F-IIST e (unzipₗ yws)
      ih2 = F-IIST e' (unzipᵣ yws)
      h4 = ≺-cong-zip ih1 ih2
   in Colist⊥.≺-trans h3 (Colist⊥.≺-trans h4 unzip-zip)

B-IIST : ∀ (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (`map-fold {A} a f g) = helper a
  where
    helper : (a : A) → B⟦ `map-fold a f g ⟧ IsIISTOf F⟦ `map-fold a f g ⟧
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (x ∷ xs) with f a .to x in eq
    ... | nothing = ⊥
    ... | just y rewrite f a .to→from eq =
          x ∷ λ where .force → helper (g a x) (force xs)
B-IIST (`delay x) = unshift-IIST x
B-IIST (`hasten x) = shift-IIST x
B-IIST (e `⋙ e') zs =
  let ih = B-IIST e' (F⟦ e ⟧ zs)
      ih' = B-IIST e zs
   in Colist⊥.≺-trans (B-incremental e ih) ih'
B-IIST (e `⊗ e') yws =
  let h1 = ≺-cong-B e (zip-unzipₗ (F⟦ e ⟧ (unzipₗ yws)) (F⟦ e' ⟧ (unzipᵣ yws)))
      h2 = ≺-cong-B e' (zip-unzipᵣ (F⟦ e ⟧ (unzipₗ yws)) (F⟦ e' ⟧ (unzipᵣ yws)))
      h3 = ≺-cong-zip h1 h2
      ih1 = B-IIST e (unzipₗ yws)
      ih2 = B-IIST e' (unzipᵣ yws)
      h4 = ≺-cong-zip ih1 ih2
   in Colist⊥.≺-trans h3 (Colist⊥.≺-trans h4 unzip-zip)

--------------------------------------------------------------------------------
-- Bundles

F-d-IST : ∀ (e : E X Y) → Is DF⟦ e ⟧ -IST F⟦ e ⟧
F-d-IST e = record
  { empty = F-empty e
  ; isIncremental = F-incremental e
  ; hasDelay = F-hasDelay e
  }

B-d-IST : ∀ (e : E X Y) → Is DB⟦ e ⟧ -IST B⟦ e ⟧
B-d-IST e = record
  { empty = B-empty e
  ; isIncremental = B-incremental e
  ; hasDelay = B-hasDelay e
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

--------------------------------------------------------------------------------
-- I invertes the semantics

≈-cong-shift : ∀ (x : A) {xs ys} → xs Colist⊥.≈ ys → shift x xs Colist⊥.≈ shift x ys
≈-cong-shift x [] = []
≈-cong-shift x ⊥ = ⊥
≈-cong-shift x (y ∷ p) = x ∷ λ where .force → ≈-cong-shift y (force p)

≈-cong-unshift : ∀ {{_ : Eq A}} (x : A) {xs ys} → xs Colist⊥.≈ ys → unshift x xs Colist⊥.≈ unshift x ys
≈-cong-unshift x [] = []
≈-cong-unshift x ⊥ = ⊥
≈-cong-unshift x (y ∷ p) with x ≟ y
... | no _ = ⊥
... | yes _ = force p

≈-cong-F : ∀ (e : E X Y) {xs ys : Colist⊥ X}
  → xs Colist⊥.≈ ys
  → F⟦ e ⟧ xs Colist⊥.≈ F⟦ e ⟧ ys
≈-cong-F {X = X} (`map-fold {A} a f g) = helper a
  where
    helper : (a : A) {xs ys : Colist⊥ X}
      → xs Colist⊥.≈ ys
      → F⟦ `map-fold a f g ⟧ xs Colist⊥.≈ F⟦ `map-fold a f g ⟧ ys
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (x ∷ p) with f a .to x
    ... | nothing = ⊥
    ... | just y = y ∷ λ where .force → helper (g a x) (force p)
≈-cong-F (`delay x) = ≈-cong-shift x
≈-cong-F (`hasten x) = ≈-cong-unshift x
≈-cong-F (e `⋙ e') = ≈-cong-F e' ∘ ≈-cong-F e
≈-cong-F (e `⊗ e') p = ≈-cong-zip (≈-cong-F e (≈-cong-unzipₗ p)) (≈-cong-F e' (≈-cong-unzipᵣ p))

≈-cong-B : ∀ (e : E X Y) {xs ys : Colist⊥ Y}
  → xs Colist⊥.≈ ys
  → B⟦ e ⟧ xs Colist⊥.≈ B⟦ e ⟧ ys
≈-cong-B {Y = Y} (`map-fold {A} a f g) = helper a
  where
    helper : (a : A) {xs ys : Colist⊥ Y}
      → xs Colist⊥.≈ ys
      → B⟦ `map-fold a f g ⟧ xs Colist⊥.≈ B⟦ `map-fold a f g ⟧ ys
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (y ∷ p) with f a .from y
    ... | nothing = ⊥
    ... | just x = x ∷ λ where .force → helper (g a x) (force p)
≈-cong-B (`delay x) = ≈-cong-unshift x
≈-cong-B (`hasten x) = ≈-cong-shift x
≈-cong-B (e `⋙ e') = ≈-cong-B e ∘ ≈-cong-B e'
≈-cong-B (e `⊗ e') p = ≈-cong-zip (≈-cong-B e (≈-cong-unzipₗ p)) (≈-cong-B e' (≈-cong-unzipᵣ p))

F∘I≡B : ∀ (e : E X Y) (ys : Colist⊥ Y)
  → F⟦ I⟦ e ⟧ ⟧ ys Colist⊥.≈ B⟦ e ⟧ ys
F∘I≡B {Y = Y} (`map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → (ys : Colist⊥ Y)
      → F⟦ I⟦ `map-fold a f g ⟧ ⟧ ys Colist⊥.≈ B⟦ `map-fold a' f g ⟧ ys
    helper _ [] = []
    helper _ ⊥ = ⊥
    helper {a} refl (y ∷ ys) with f a .from y in eq
    ... | nothing = ⊥
    ... | just x =
          x ∷ λ where .force → helper (cong (maybe (g a) a) eq) (force ys)
F∘I≡B (`delay x) ys = Colist⊥.≈-refl
F∘I≡B (`hasten x) ys = Colist⊥.≈-refl
F∘I≡B (e `⋙ e') ys =
  let ih = F∘I≡B e' ys
      ih' = F∘I≡B e (F⟦ I⟦ e' ⟧ ⟧ ys)
   in Colist⊥.≈-trans ih' (≈-cong-B e ih)
F∘I≡B (e `⊗ e') yws =
  let ih = F∘I≡B e (unzipₗ yws)
      ih' = F∘I≡B e' (unzipᵣ yws)
   in ≈-cong-zip ih ih'

B∘I≡F : ∀ (e : E X Y) (xs : Colist⊥ X)
  → B⟦ I⟦ e ⟧ ⟧ xs Colist⊥.≈ F⟦ e ⟧ xs
B∘I≡F {X = X} (`map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → (xs : Colist⊥ X)
      → B⟦ I⟦ `map-fold a f g ⟧ ⟧ xs Colist⊥.≈ F⟦ `map-fold a' f g ⟧ xs
    helper _ [] = []
    helper _ ⊥ = ⊥
    helper {a} refl (x ∷ xs) with f a .to x in eq
    ... | nothing = ⊥
    ... | just y =
          y ∷ λ where .force → helper (cong (maybe (g a) a) (f a .to→from eq)) (force xs)
B∘I≡F (`delay x) xs = Colist⊥.≈-refl
B∘I≡F (`hasten x) xs = Colist⊥.≈-refl
B∘I≡F (e `⋙ e') xs =
  let ih = B∘I≡F e xs
      ih' = B∘I≡F e' (B⟦ I⟦ e ⟧ ⟧ xs)
   in Colist⊥.≈-trans ih' (≈-cong-F e' ih)
B∘I≡F (e `⊗ e') xzs =
  let ih = B∘I≡F e (unzipₗ xzs)
      ih' = B∘I≡F e' (unzipᵣ xzs)
   in ≈-cong-zip ih ih'
