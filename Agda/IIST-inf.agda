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

open import Codata.PartialStream
open import IIST.Common
open import IIST.Syntax

private
  variable
    A B X Y Z W : Set

-------------------------------------------------------------------------------
-- Additional operations on partial streams

shift : A → Stream⊥ A → Stream⊥ A
shift x (y ∷ xs) = x ∷ λ where .force → shift y (force xs)
shift x ⊥ = x ∷ λ where .force → ⊥

unshift : {{_ : Eq A}} → A → Stream⊥ A → Stream⊥ A
unshift x (y ∷ xs) with x ≟ y
... | no _ = ⊥
... | yes _ = force xs
unshift x ⊥ = ⊥

≈-cong-shift : ∀ (x : A) {xs ys} → xs ≈ ys → shift x xs ≈ shift x ys
≈-cong-shift x (y ∷ p) = x ∷ λ where .force → ≈-cong-shift y (force p)
≈-cong-shift x ⊥ = x ∷ λ where .force → ⊥

≈-cong-unshift : ∀ {{_ : Eq A}} (x : A) {xs ys}
  → xs ≈ ys
  → unshift x xs ≈ unshift x ys
≈-cong-unshift x (y ∷ p) with x ≟ y
... | no _ = ⊥
... | yes refl = force p
≈-cong-unshift x ⊥ = ⊥

shift-⊑-∷ : ∀ (x : A) {xs} → shift x xs ⊑ x ∷ delay xs
shift-⊑-∷ x {y ∷ xs} = x ∷ λ where .force → shift-⊑-∷ y
shift-⊑-∷ x {⊥} = x ∷ λ where .force → ⊥ₗ

⊑-cong-shift : ∀ (x : A) {xs ys} → xs ⊑ ys → shift x xs ⊑ shift x ys
⊑-cong-shift x (y ∷ p) = x ∷ λ where .force → ⊑-cong-shift y (force p)
⊑-cong-shift x {ys = _ ∷ _} ⊥ₗ = x ∷ λ where .force → ⊥ₗ
⊑-cong-shift x {ys = ⊥} ⊥ₗ = x ∷ λ where .force → ⊥ₗ

⊑-cong-unshift : ∀ {{_ : Eq A}} (x : A) {xs ys}
  → xs ⊑ ys
  → unshift x xs ⊑ unshift x ys
⊑-cong-unshift x (y ∷ p) with x ≟ y
... | no _ = ⊥ₗ
... | yes refl = force p
⊑-cong-unshift x ⊥ₗ = ⊥ₗ

no⊥-shift⁻¹ : ∀ (x : A) {xs} → No⊥ (shift x xs) → No⊥ xs
no⊥-shift⁻¹ x {y ∷ xs} (_ ∷ p) = y ∷ λ where .force → no⊥-shift⁻¹ y (force p)
no⊥-shift⁻¹ x {⊥} (_ ∷ p) with () ← force p

no⊥-unshift⁻¹ : ∀ {{_ : Eq A}} (x : A) {xs} → No⊥ (unshift x xs) → No⊥ xs
no⊥-unshift⁻¹ x {y ∷ xs} p with x ≟ y
no⊥-unshift⁻¹ x {y ∷ xs} () | no _
no⊥-unshift⁻¹ x {x ∷ xs} p  | yes refl = x ∷ λ where .force → p

-------------------------------------------------------------------------------
-- Sequence transformation

ST : Set → Set → Set
ST X Y = Stream⊥ X → Stream⊥ Y

_IsIISTOf_ : ST X Y → ST Y X → Set
st' IsIISTOf st = ∀ {xs} → No⊥ (st xs) → st' (st xs) ⊑ xs

-------------------------------------------------------------------------------
-- IIST constructors and semantics

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST X Y
F-map-fold a f g (x ∷ xs) with f a .to x
... | nothing = ⊥
... | just y = y ∷ λ where .force → F-map-fold (g a x) f g (force xs)
F-map-fold a f g ⊥ = ⊥

F⟦_⟧ : E X Y → ST X Y
F⟦ map-fold a f g ⟧ = F-map-fold a f g
F⟦ delay x ⟧ = shift x
F⟦ hasten x ⟧ = unshift x
F⟦ e ⟫ e' ⟧ = F⟦ e' ⟧ ∘ F⟦ e ⟧
F⟦ e ⊗ e' ⟧ xzs = zip (F⟦ e ⟧ (map proj₁ xzs)) (F⟦ e' ⟧ (map proj₂ xzs))

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST Y X
B-map-fold a f g (y ∷ ys) with f a .from y
... | nothing = ⊥
... | just x = x ∷ λ where .force → B-map-fold (g a x) f g (force ys)
B-map-fold a f g ⊥ = ⊥

B⟦_⟧ : E X Y → ST Y X
B⟦ map-fold a f g ⟧ = B-map-fold a f g
B⟦ delay x ⟧ = unshift x
B⟦ hasten x ⟧ = shift x
B⟦ e ⟫ e' ⟧ = B⟦ e ⟧ ∘ B⟦ e' ⟧
B⟦ e ⊗ e' ⟧ xzs = zip (B⟦ e ⟧ (map proj₁ xzs)) (B⟦ e' ⟧ (map proj₂ xzs))

--------------------------------------------------------------------------------
-- F⟦_⟧ and B⟦_⟧ are inverse of each other

no⊥-F⁻¹ : ∀ (e : E X Y) {xs} → No⊥ (F⟦ e ⟧ xs) → No⊥ xs
no⊥-F⁻¹ (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) {xs} → No⊥ (F⟦ map-fold a f g ⟧ xs) → No⊥ xs
    helper a {x ∷ xs} p with f a .to x
    helper a {x ∷ xs} () | nothing
    helper a {x ∷ xs} (_ ∷ p) | just y = x ∷ λ where .force → helper (g a x) (force p)
no⊥-F⁻¹ (delay x) = no⊥-shift⁻¹ x
no⊥-F⁻¹ (hasten x) = no⊥-unshift⁻¹ x
no⊥-F⁻¹ (e ⟫ e') = no⊥-F⁻¹ e ∘ no⊥-F⁻¹ e'
no⊥-F⁻¹ (e ⊗ e') p = no⊥-map⁻¹ (no⊥-F⁻¹ e (no⊥-zip⁻¹ₗ p))

no⊥-B⁻¹ : ∀ (e : E X Y) {ys} → No⊥ (B⟦ e ⟧ ys) → No⊥ ys
no⊥-B⁻¹ (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) {ys} → No⊥ (B⟦ map-fold a f g ⟧ ys) → No⊥ ys
    helper a {y ∷ ys} p with f a .from y
    helper a {y ∷ ys} () | nothing
    helper a {y ∷ ys} (_ ∷ p) | just x = y ∷ λ where .force → helper (g a x) (force p)
no⊥-B⁻¹ (delay x) = no⊥-unshift⁻¹ x
no⊥-B⁻¹ (hasten x) = no⊥-shift⁻¹ x
no⊥-B⁻¹ (e ⟫ e') = no⊥-B⁻¹ e' ∘ no⊥-B⁻¹ e
no⊥-B⁻¹ (e ⊗ e') p = no⊥-map⁻¹ (no⊥-B⁻¹ e (no⊥-zip⁻¹ₗ p))

⊑-cong-F : ∀ (e : E X Y) {xs ys} → xs ⊑ ys → F⟦ e ⟧ xs ⊑ F⟦ e ⟧ ys
⊑-cong-F (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) {xs ys}
      → xs ⊑ ys
      → F⟦ map-fold a f g ⟧ xs ⊑ F⟦ map-fold a f g ⟧ ys
    helper a (x ∷ p) with f a .to x
    ... | nothing = ⊥ₗ
    ... | just y = y ∷ λ where .force → helper (g a x) (force p)
    helper a ⊥ₗ = ⊥ₗ
⊑-cong-F (delay x) = ⊑-cong-shift x
⊑-cong-F (hasten x) = ⊑-cong-unshift x
⊑-cong-F (e ⟫ e') = ⊑-cong-F e' ∘ ⊑-cong-F e
⊑-cong-F (e ⊗ e') p = ⊑-cong-zip (⊑-cong-F e (⊑-cong-map p)) (⊑-cong-F e' (⊑-cong-map p))

⊑-cong-B : ∀ (e : E X Y) {xs ys} → xs ⊑ ys → B⟦ e ⟧ xs ⊑ B⟦ e ⟧ ys
⊑-cong-B (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) {xs ys}
      → xs ⊑ ys
      → B⟦ map-fold a f g ⟧ xs ⊑ B⟦ map-fold a f g ⟧ ys
    helper a (y ∷ p) with f a .from y
    ... | nothing = ⊥ₗ
    ... | just x = x ∷ λ where .force → helper (g a x) (force p)
    helper a ⊥ₗ = ⊥ₗ
⊑-cong-B (delay x) = ⊑-cong-unshift x
⊑-cong-B (hasten x) = ⊑-cong-shift x
⊑-cong-B (e ⟫ e') = ⊑-cong-B e ∘ ⊑-cong-B e'
⊑-cong-B (e ⊗ e') p = ⊑-cong-zip (⊑-cong-B e (⊑-cong-map p)) (⊑-cong-B e' (⊑-cong-map p))

shift-IIST : ∀ {{_ : Eq A}} (x : A) → shift x IsIISTOf unshift x
shift-IIST x {y ∷ xs} p with x ≟ y
shift-IIST x {y ∷ xs} () | no _
shift-IIST x {y ∷ xs} p  | yes refl = shift-⊑-∷ x

unshift-IIST : ∀ {{_ : Eq A}} (x : A) → unshift x IsIISTOf shift x
unshift-IIST x {y ∷ xs} p with x ≟ x
... | no contra with () ← contra refl
... | yes refl = shift-⊑-∷ y
unshift-IIST x {⊥} p with x ≟ x
... | no contra with () ← contra refl
... | yes refl = ⊥ₗ

F-IIST : ∀ (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → F⟦ map-fold a f g ⟧ IsIISTOf B⟦ map-fold a f g ⟧
    helper a {y ∷ ys} p with f a .from y in eq
    helper a {y ∷ ys} () | nothing
    helper a {y ∷ ys} (_ ∷ p) | just x rewrite f a .from→to eq =
      y ∷ λ where .force → helper (g a x) (force p)
F-IIST (delay x) = shift-IIST x
F-IIST (hasten x) = unshift-IIST x
F-IIST (e ⟫ e') p =
  let ih = F-IIST e p
      ih' = F-IIST e' (no⊥-B⁻¹ e p)
   in ⊑-trans (⊑-cong-F e' ih) ih'
F-IIST (e ⊗ e') {yws} p =
  let lem1 = ⊑-cong-F e (⊑-zip-unzipₗ {xs = B⟦ e ⟧ (map proj₁ yws)} {B⟦ e' ⟧ (map proj₂ yws)})
      lem2 = ⊑-cong-F e' (⊑-zip-unzipᵣ {xs = B⟦ e ⟧ (map proj₁ yws)} {B⟦ e' ⟧ (map proj₂ yws)})
      lem3 = ⊑-cong-zip lem1 lem2
      lem4 = ⊑-cong-zip (F-IIST e (no⊥-zip⁻¹ₗ p)) (F-IIST e' (no⊥-zip⁻¹ᵣ p))
      lem5 = ⊑-trans lem3 lem4
   in ⊑-trans lem3 (⊑-trans lem4 ⊑-unzip-zip)

B-IIST : ∀ (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → B⟦ map-fold a f g ⟧ IsIISTOf F⟦ map-fold a f g ⟧
    helper a {x ∷ xs} p with f a .to x in eq
    helper a {x ∷ xs} () | nothing
    helper a {x ∷ xs} (_ ∷ p) | just y rewrite f a .to→from eq =
      x ∷ λ where .force → helper (g a x) (force p)
B-IIST (delay x) = unshift-IIST x
B-IIST (hasten x) = shift-IIST x
B-IIST (e ⟫ e') p =
  let ih = B-IIST e' p
      ih' = B-IIST e (no⊥-F⁻¹ e' p)
   in ⊑-trans (⊑-cong-B e ih) ih'
B-IIST (e ⊗ e') {yws} p =
  let lem1 = ⊑-cong-B e (⊑-zip-unzipₗ {xs = F⟦ e ⟧ (map proj₁ yws)} {F⟦ e' ⟧ (map proj₂ yws)})
      lem2 = ⊑-cong-B e' (⊑-zip-unzipᵣ {xs = F⟦ e ⟧ (map proj₁ yws)} {F⟦ e' ⟧ (map proj₂ yws)})
      lem3 = ⊑-cong-zip lem1 lem2
      lem4 = ⊑-cong-zip (B-IIST e (no⊥-zip⁻¹ₗ p)) (B-IIST e' (no⊥-zip⁻¹ᵣ p))
      lem5 = ⊑-trans lem3 lem4
   in ⊑-trans lem3 (⊑-trans lem4 ⊑-unzip-zip)

--------------------------------------------------------------------------------
-- Properties of I⟦_⟧

≈-cong-F : ∀ (e : E X Y) {xs ys}
  → xs ≈ ys
  → F⟦ e ⟧ xs ≈ F⟦ e ⟧ ys
≈-cong-F {X} (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) {xs ys}
      → xs ≈ ys
      → F⟦ map-fold a f g ⟧ xs ≈ F⟦ map-fold a f g ⟧ ys
    helper a (x ∷ p) with f a .to x
    ... | nothing = ⊥
    ... | just y = y ∷ λ where .force → helper (g a x) (force p)
    helper a ⊥ = ⊥
≈-cong-F (delay x) = ≈-cong-shift x
≈-cong-F (hasten x) = ≈-cong-unshift x
≈-cong-F (e ⟫ e') = ≈-cong-F e' ∘ ≈-cong-F e
≈-cong-F (e ⊗ e') p = ≈-cong-zip (≈-cong-F e (≈-cong-map p)) (≈-cong-F e' (≈-cong-map p))

≈-cong-B : ∀ (e : E X Y) {xs ys}
  → xs ≈ ys
  → B⟦ e ⟧ xs ≈ B⟦ e ⟧ ys
≈-cong-B {X} (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) {xs ys}
      → xs ≈ ys
      → B⟦ map-fold a f g ⟧ xs ≈ B⟦ map-fold a f g ⟧ ys
    helper a (y ∷ p) with f a .from y
    ... | nothing = ⊥
    ... | just x = x ∷ λ where .force → helper (g a x) (force p)
    helper a ⊥ = ⊥
≈-cong-B (delay x) = ≈-cong-unshift x
≈-cong-B (hasten x) = ≈-cong-shift x
≈-cong-B (e ⟫ e') = ≈-cong-B e ∘ ≈-cong-B e'
≈-cong-B (e ⊗ e') p = ≈-cong-zip (≈-cong-B e (≈-cong-map p)) (≈-cong-B e' (≈-cong-map p))

F∘I≈B : ∀ (e : E X Y) ys
  → F⟦ I⟦ e ⟧ ⟧ ys ≈ B⟦ e ⟧ ys
F∘I≈B {Y = Y} (map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → (ys : Stream⊥ Y)
      → F⟦ I⟦ map-fold a f g ⟧ ⟧ ys ≈ B⟦ map-fold a' f g ⟧ ys
    helper _ ⊥ = ⊥
    helper {a} refl (y ∷ ys) with f a .from y in eq
    ... | nothing = ⊥
    ... | just x =
          x ∷ λ where .force → helper (cong (maybe (g a) a) eq) (force ys)
F∘I≈B (delay x) ys = ≈-refl
F∘I≈B (hasten x) ys = ≈-refl
F∘I≈B (e ⟫ e') ys =
  let ih = F∘I≈B e' ys
      ih' = F∘I≈B e (F⟦ I⟦ e' ⟧ ⟧ ys)
   in ≈-trans ih' (≈-cong-B e ih)
F∘I≈B (e ⊗ e') ys = ≈-cong-zip (F∘I≈B e (map proj₁ ys)) (F∘I≈B e' (map proj₂ ys))

B∘I≈F : ∀ (e : E X Y) xs
  → B⟦ I⟦ e ⟧ ⟧ xs ≈ F⟦ e ⟧ xs
B∘I≈F {X} (map-fold {A} a f g) = helper refl
  where
    helper : ∀ {a a' : A} → a ≡ a' → (xs : Stream⊥ X)
      → B⟦ I⟦ map-fold a f g ⟧ ⟧ xs ≈ F⟦ map-fold a' f g ⟧ xs
    helper _ ⊥ = ⊥
    helper {a} refl (x ∷ xs) with f a .to x in eq
    ... | nothing = ⊥
    ... | just y =
          y ∷ λ where .force → helper (cong (maybe (g a) a) (f a .to→from eq)) (force xs)
B∘I≈F (delay x) ys = ≈-refl
B∘I≈F (hasten x) ys = ≈-refl
B∘I≈F (e ⟫ e') ys =
  let ih = B∘I≈F e ys
      ih' = B∘I≈F e' (B⟦ I⟦ e ⟧ ⟧ ys)
   in ≈-trans ih' (≈-cong-F e' ih)
B∘I≈F (e ⊗ e') ys = ≈-cong-zip (B∘I≈F e (map proj₁ ys)) (B∘I≈F e' (map proj₂ ys))
