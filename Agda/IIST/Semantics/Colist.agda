{-# OPTIONS --guardedness #-}

module IIST.Semantics.Colist where

open import Data.Maybe.Base using ( Maybe; just; nothing; maybe )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Nat.Properties using ( +-identityʳ; +-comm )
open import Data.Product.Base using ( _×_; _,_; proj₁; proj₂ )
open import Data.Unit.Base using ( ⊤; tt )
open import Function using ( _∘_ )
open import Relation.Binary.Core using ( _=[_]⇒_ )
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary using ( ¬_; yes; no )

open import Codata.PartialColist as Colist⊥
open import Codata.PartialConat as Coℕ⊥
open import IIST.Common
open import IIST.Syntax

private
  variable
    A B X Y Z W : Set
    k : PrefixKind

-------------------------------------------------------------------------------
-- Sequence transformation

ST : Set → Set → Set
ST X Y = Colist⊥ X → Colist⊥ Y

IsIncremental : ST X Y → Set
IsIncremental st = _≺_ =[ st ]⇒ _≺_

HasDelay : ℕ → ST X Y → Set
HasDelay d st = ∀ xs → colength (st xs) ⊑ (colength xs ∸ℕ d)

record Is_-IST_ (d : ℕ) (st : ST X Y) : Set where
  field
    empty : st [] ≡ []
    isIncremental : IsIncremental st
    hasDelay : HasDelay d st

_IsIISTOf_ : ST X Y → ST Y X → Set
st' IsIISTOf st = ∀ xs → st' (st xs) ≺≺ xs

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

-- parallel composition
_⊗_ : ST X Y → ST Z W → ST (X × Z) (Y × W)
(f ⊗ g) xzs = zip (f (unzipₗ xzs)) (g (unzipᵣ xzs))

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
F⟦ e `⊗ e' ⟧ = F⟦ e ⟧ ⊗ F⟦ e' ⟧

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
B⟦ e `⊗ e' ⟧ = B⟦ e ⟧ ⊗ B⟦ e' ⟧

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

prefix-cong-shift : ∀ (x : A) → Prefix k =[ shift x ]⇒ Prefix k
prefix-cong-shift x [] = []
prefix-cong-shift x ⊥ = ⊥
prefix-cong-shift x ⊥ₗ = ⊥ₗ
prefix-cong-shift x (y ∷ p) = x ∷ λ where .force → prefix-cong-shift y (force p)

prefix-cong-unshift : ∀ {{_ : Eq A}} (x : A) → Prefix k =[ unshift x ]⇒ Prefix k
prefix-cong-unshift x [] = []
prefix-cong-unshift x ⊥ = ⊥
prefix-cong-unshift x ⊥ₗ = ⊥ₗ
prefix-cong-unshift x (y ∷ p) with x ≟ y
prefix-cong-unshift x (y ∷ p) | yes _ = force p
prefix-cong-unshift {k = ⊥≺⊥} x (_ ∷ p) | no _ = ⊥
prefix-cong-unshift {k = ⊥≺xs} x (_ ∷ p) | no _ = ⊥ₗ

prefix-cong-⊗ : ∀ {f : ST X Y} {g : ST Z W}
  → Prefix k =[ f ]⇒ Prefix k
  → Prefix k =[ g ]⇒ Prefix k
  → Prefix k =[ f ⊗ g ]⇒ Prefix k
prefix-cong-⊗ p q r = prefix-cong-zip (p (prefix-cong-unzipₗ r)) (q (prefix-cong-unzipᵣ r))

prefix-cong-F : ∀ (e : E X Y) → Prefix k =[ F⟦ e ⟧ ]⇒ Prefix k
prefix-cong-F (`map-fold a f g) = helper a
  where
    helper : ∀ a → Prefix k =[ F⟦ `map-fold a f g ⟧ ]⇒ Prefix k
    helper a [] = []
    helper a ⊥ = ⊥
    helper a ⊥ₗ = ⊥ₗ
    helper a (x ∷ p) with f a .to x
    helper a (x ∷ p) | just y = y ∷ λ where .force → helper (g a x) (force p)
    helper {⊥≺⊥} a (_ ∷ p) | nothing = ⊥
    helper {⊥≺xs} a (_ ∷ p) | nothing = ⊥ₗ
prefix-cong-F (`delay x) = prefix-cong-shift x
prefix-cong-F (`hasten x) = prefix-cong-unshift x
prefix-cong-F (e `⋙ e') = prefix-cong-F e' ∘ prefix-cong-F e
prefix-cong-F (e `⊗ e') = prefix-cong-⊗ (prefix-cong-F e) (prefix-cong-F e')

prefix-cong-B : ∀ (e : E X Y) → Prefix k =[ B⟦ e ⟧ ]⇒ Prefix k
prefix-cong-B (`map-fold a f g) = helper a
  where
    helper : ∀ a → Prefix k =[ B⟦ `map-fold a f g ⟧ ]⇒ Prefix k
    helper a [] = []
    helper a ⊥ = ⊥
    helper a ⊥ₗ = ⊥ₗ
    helper a (y ∷ p) with f a .from y
    helper a (y ∷ p) | just x = x ∷ λ where .force → helper (g a x) (force p)
    helper {⊥≺⊥} a (_ ∷ p) | nothing = ⊥
    helper {⊥≺xs} a (_ ∷ p) | nothing = ⊥ₗ
prefix-cong-B (`delay x) = prefix-cong-unshift x
prefix-cong-B (`hasten x) = prefix-cong-shift x
prefix-cong-B (e `⋙ e') = prefix-cong-B e ∘ prefix-cong-B e'
prefix-cong-B (e `⊗ e') = prefix-cong-⊗ (prefix-cong-B e) (prefix-cong-B e')

F-incremental : ∀ (e : E X Y) → IsIncremental F⟦ e ⟧
F-incremental = prefix-cong-F

B-incremental : ∀ (e : E X Y) → IsIncremental B⟦ e ⟧
B-incremental = prefix-cong-B

--------------------------------------------------------------------------------
-- d-Incrementality of F and B

module _ where
  open ⊑-Reasoning

  shift-hasDelay : ∀ (x : A) → HasDelay 0 (shift x)
  shift-hasDelay x [] = zero
  shift-hasDelay x ⊥ = ⊥ₗ
  shift-hasDelay x (y ∷ xs) = suc λ where .force → shift-hasDelay y (force xs)

  unshift-hasDelay : ∀ {{_ : Eq A}} (x : A) → HasDelay 1 (unshift x)
  unshift-hasDelay x [] = zero
  unshift-hasDelay x ⊥ = ⊥ₗ
  unshift-hasDelay x (y ∷ xs) with x ≟ y
  ... | no _ = ⊥ₗ
  ... | yes _ = ⊑-refl

  ∘-hasDelay : ∀ {f : ST Y Z} {g : ST X Y} d d'
    → HasDelay d f
    → HasDelay d' g
    → HasDelay (d' + d) (f ∘ g)
  ∘-hasDelay {f = f} {g} d d' p q xs =
    begin
      colength (f (g xs))
    ≲⟨ p (g xs) ⟩
      colength (g xs) ∸ℕ d
    ≲⟨ ⊑-cong-∸ℕ d (q xs) ⟩
      colength xs ∸ℕ d' ∸ℕ d
    ≈⟨ ∸ℕ-+-assoc (colength xs) d' d ⟩
      colength xs ∸ℕ (d' + d)
    ∎

  ⊗-hasDelay : ∀ {f : ST X Y} {g : ST Z W} d d'
    → HasDelay d f
    → HasDelay d' g
    → HasDelay (d ⊔ d') (f ⊗ g)
  ⊗-hasDelay {f = f} {g} d d' p q xzs =
    begin
      colength (zip (f (unzipₗ xzs)) (g (unzipᵣ xzs)))
    ≈⟨ colength-zip ⟩
      colength (f (unzipₗ xzs)) ⊓ colength (g (unzipᵣ xzs))
    ≲⟨ ⊑-cong-⊓ (p (unzipₗ xzs)) (q (unzipᵣ xzs)) ⟩
      (colength (unzipₗ xzs) ∸ℕ d) ⊓ (colength (unzipᵣ xzs) ∸ℕ d')
    ≈⟨ ≈-cong-⊓ (≈-cong-∸ℕ d colength-unzipₗ) (≈-cong-∸ℕ d' colength-unzipᵣ) ⟩
      (colength xzs ∸ℕ d) ⊓ (colength xzs ∸ℕ d')
    ≈⟨ Coℕ⊥.≈-sym (∸ℕ-distribˡ-⊔-⊓ (colength xzs) d d') ⟩
      colength xzs ∸ℕ (d ⊔ d')
    ∎

  F-hasDelay : ∀ (e : E X Y) → HasDelay DF⟦ e ⟧ F⟦ e ⟧
  F-hasDelay (`map-fold a f g) = helper a
    where
      helper : ∀ a → HasDelay 0 F⟦ `map-fold a f g ⟧
      helper a [] = zero
      helper a ⊥ = ⊥ₗ
      helper a (x ∷ xs) with f a .to x
      ... | nothing = ⊥ₗ
      ... | just y = suc λ where .force → helper (g a x) (force xs)
  F-hasDelay (`delay x) = shift-hasDelay x
  F-hasDelay (`hasten x) = unshift-hasDelay x
  F-hasDelay (e `⋙ e') = ∘-hasDelay DF⟦ e' ⟧ DF⟦ e ⟧ (F-hasDelay e') (F-hasDelay e)
  F-hasDelay (e `⊗ e') = ⊗-hasDelay DF⟦ e ⟧ DF⟦ e' ⟧ (F-hasDelay e) (F-hasDelay e')

  B-hasDelay : ∀ (e : E X Y) → HasDelay DB⟦ e ⟧ B⟦ e ⟧
  B-hasDelay (`map-fold a f g) = helper a
    where
      helper : ∀ a → HasDelay 0 B⟦ `map-fold a f g ⟧
      helper a [] = zero
      helper a ⊥ = ⊥ₗ
      helper a (y ∷ ys) with f a .from y
      ... | nothing = ⊥ₗ
      ... | just x = suc λ where .force → helper (g a x) (force ys)
  B-hasDelay (`delay x) = unshift-hasDelay x
  B-hasDelay (`hasten x) = shift-hasDelay x
  B-hasDelay (e `⋙ e') = ∘-hasDelay DB⟦ e ⟧ DB⟦ e' ⟧ (B-hasDelay e) (B-hasDelay e')
  B-hasDelay (e `⊗ e') = ⊗-hasDelay DB⟦ e ⟧ DB⟦ e' ⟧ (B-hasDelay e) (B-hasDelay e')

--------------------------------------------------------------------------------
-- F⟦_⟧ and B⟦_⟧ are inverse of each other

shift-≺≺-∷ : ∀ (x : A) xs → shift x xs ≺≺ x ∷ delay xs
shift-≺≺-∷ x [] = []
shift-≺≺-∷ x ⊥ = ⊥ₗ
shift-≺≺-∷ x (y ∷ xs) = x ∷ λ where .force → shift-≺≺-∷ y (force xs)

shift-IIST : ∀ {{_ : Eq X}} (x : X) → shift x IsIISTOf unshift x
shift-IIST x [] = []
shift-IIST x ⊥ = ⊥ₗ
shift-IIST x (y ∷ xs) with x ≟ y
... | no _ = ⊥ₗ
... | yes refl = shift-≺≺-∷ x (force xs)

unshift-IIST : ∀ {{_ : Eq X}} (x : X) → unshift x IsIISTOf shift x
unshift-IIST x [] = []
unshift-IIST x ⊥ = ⊥ₗ
unshift-IIST x (y ∷ xs) with x ≟ x
... | no ¬refl with () ← ¬refl refl
... | yes refl = shift-≺≺-∷ y (force xs)

∘-IIST : ∀ {f : ST Y Z} {f' : ST Z Y} {g : ST X Y} {g' : ST Y X}
  → f IsIISTOf f'
  → g IsIISTOf g'
  → _≺≺_ =[ f ]⇒ _≺≺_
  → (f ∘ g) IsIISTOf (g' ∘ f')
∘-IIST {f = f} {f'} {g} {g'} f-inv-f' g-inv-g' f-inc zs =
  begin
    f (g (g' (f' zs)))
  ≲⟨ f-inc (g-inv-g' (f' zs)) ⟩
    f (f' zs)
  ≲⟨ f-inv-f' zs ⟩
    zs
  ∎
  where open PrefixReasoning

⊗-IIST : ∀ {f : ST X Y} {f' : ST Y X} {g : ST Z W} {g' : ST W Z}
  → f IsIISTOf f'
  → g IsIISTOf g'
  → _≺≺_ =[ f ]⇒ _≺≺_
  → _≺≺_ =[ g ]⇒ _≺≺_
  → (f ⊗ g) IsIISTOf (f' ⊗ g')
⊗-IIST {f = f} {f'} {g} {g'} f-inv-f' g-inv-g' f-inc g-inc yws =
  begin
    (f ⊗ g) ((f' ⊗ g') yws)
  ≡⟨⟩
    zip
      (f (unzipₗ (zip (f' (unzipₗ yws)) (g' (unzipᵣ yws)))))
      (g (unzipᵣ (zip (f' (unzipₗ yws)) (g' (unzipᵣ yws)))))
  ≲⟨ prefix-cong-zip
      (f-inc (zip-unzipₗ (f' (unzipₗ yws)) (g' (unzipᵣ yws))))
      (g-inc (zip-unzipᵣ (f' (unzipₗ yws)) (g' (unzipᵣ yws))))
   ⟩
    zip (f (f' (unzipₗ yws))) (g (g' (unzipᵣ yws)))
  ≲⟨ prefix-cong-zip (f-inv-f' (unzipₗ yws)) (g-inv-g' (unzipᵣ yws)) ⟩
    zip (unzipₗ yws) (unzipᵣ yws)
  ≈⟨ unzip-zip ⟩
    yws
  ∎
  where open PrefixReasoning

F-IIST : ∀ (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (`map-fold a f g) = helper a
  where
    helper : ∀ a → F⟦ `map-fold a f g ⟧ IsIISTOf B⟦ `map-fold a f g ⟧
    helper a [] = []
    helper a ⊥ = ⊥ₗ
    helper a (y ∷ ys) with f a .from y in eq
    ... | nothing = ⊥ₗ
    ... | just x rewrite f a .from→to eq =
          y ∷ λ where .force → helper (g a x) (force ys)
F-IIST (`delay x) = shift-IIST x
F-IIST (`hasten x) = unshift-IIST x
F-IIST (e `⋙ e') = ∘-IIST {g = F⟦ e ⟧} (F-IIST e') (F-IIST e) (prefix-cong-F e')
F-IIST (e `⊗ e') = ⊗-IIST (F-IIST e) (F-IIST e') (prefix-cong-F e) (prefix-cong-F e')

B-IIST : ∀ (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (`map-fold a f g) = helper a
  where
    helper : ∀ a → B⟦ `map-fold a f g ⟧ IsIISTOf F⟦ `map-fold a f g ⟧
    helper a [] = []
    helper a ⊥ = ⊥ₗ
    helper a (x ∷ xs) with f a .to x in eq
    ... | nothing = ⊥ₗ
    ... | just y rewrite f a .to→from eq =
          x ∷ λ where .force → helper (g a x) (force xs)
B-IIST (`delay x) = unshift-IIST x
B-IIST (`hasten x) = shift-IIST x
B-IIST (e `⋙ e') = ∘-IIST {g = B⟦ e' ⟧} (B-IIST e) (B-IIST e') (prefix-cong-B e)
B-IIST (e `⊗ e') = ⊗-IIST (B-IIST e) (B-IIST e') (prefix-cong-B e) (prefix-cong-B e')

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
-- I inverts the semantics

≈-cong-shift : ∀ (x : A) → Colist⊥._≈_ =[ shift x ]⇒ Colist⊥._≈_
≈-cong-shift x [] = []
≈-cong-shift x ⊥ = ⊥
≈-cong-shift x (y ∷ p) = x ∷ λ where .force → ≈-cong-shift y (force p)

≈-cong-unshift : ∀ {{_ : Eq A}} (x : A) → Colist⊥._≈_ =[ unshift x ]⇒ Colist⊥._≈_
≈-cong-unshift x [] = []
≈-cong-unshift x ⊥ = ⊥
≈-cong-unshift x (y ∷ p) with x ≟ y
... | no _ = ⊥
... | yes _ = force p

≈-cong-F : ∀ (e : E X Y) → Colist⊥._≈_ =[ F⟦ e ⟧ ]⇒ Colist⊥._≈_
≈-cong-F (`map-fold a f g) = helper a
  where
    helper : ∀ a → Colist⊥._≈_ =[ F⟦ `map-fold a f g ⟧ ]⇒ Colist⊥._≈_
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (x ∷ p) with f a .to x
    ... | nothing = ⊥
    ... | just y = y ∷ λ where .force → helper (g a x) (force p)
≈-cong-F (`delay x) = ≈-cong-shift x
≈-cong-F (`hasten x) = ≈-cong-unshift x
≈-cong-F (e `⋙ e') = ≈-cong-F e' ∘ ≈-cong-F e
≈-cong-F (e `⊗ e') p = ≈-cong-zip (≈-cong-F e (≈-cong-unzipₗ p)) (≈-cong-F e' (≈-cong-unzipᵣ p))

≈-cong-B : ∀ (e : E X Y) → Colist⊥._≈_ =[ B⟦ e ⟧ ]⇒ Colist⊥._≈_
≈-cong-B (`map-fold a f g) = helper a
  where
    helper : ∀ a → Colist⊥._≈_ =[ B⟦ `map-fold a f g ⟧ ]⇒ Colist⊥._≈_
    helper a [] = []
    helper a ⊥ = ⊥
    helper a (y ∷ p) with f a .from y
    ... | nothing = ⊥
    ... | just x = x ∷ λ where .force → helper (g a x) (force p)
≈-cong-B (`delay x) = ≈-cong-unshift x
≈-cong-B (`hasten x) = ≈-cong-shift x
≈-cong-B (e `⋙ e') = ≈-cong-B e ∘ ≈-cong-B e'
≈-cong-B (e `⊗ e') p = ≈-cong-zip (≈-cong-B e (≈-cong-unzipₗ p)) (≈-cong-B e' (≈-cong-unzipᵣ p))

F∘I≡B : ∀ (e : E X Y) ys → F⟦ I⟦ e ⟧ ⟧ ys Colist⊥.≈ B⟦ e ⟧ ys
F∘I≡B (`map-fold a f g) = helper refl
  where
    helper : ∀ {a a'} → a ≡ a' → ∀ ys
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

B∘I≡F : ∀ (e : E X Y) xs → B⟦ I⟦ e ⟧ ⟧ xs Colist⊥.≈ F⟦ e ⟧ xs
B∘I≡F (`map-fold a f g) = helper refl
  where
    helper : ∀ {a a'} → a ≡ a' → ∀ xs
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
