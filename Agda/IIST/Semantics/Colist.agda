{-# OPTIONS --guardedness --cubical #-}

module IIST.Semantics.Colist where

open import Cubical.Foundations.Everything hiding ( empty; _∎; step-≡; _≡⟨⟩_ )
open import Cubical.Data.Empty as Empty using () renaming ( ⊥ to Empty )
open import Cubical.Data.Equality using ( pathToEq ) renaming ( _≡_ to _≡′_; refl to refl′ )
open import Cubical.Data.Maybe.Base as Maybe using ( Maybe; just; nothing )
open import Cubical.Data.Maybe.Properties using ( ¬nothing≡just; just-inj )
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Nat.Properties using () renaming ( max to _⊔_ )
open import Cubical.Data.Sigma.Base using ( _×_; _,_; fst; snd )
open import Cubical.Data.Unit.Base using ( Unit; tt )
open import Cubical.Relation.Nullary.Base using ( ¬_; yes; no )

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
IsIncremental st = ∀ {xs ys} → xs ≺ ys → st xs ≺ st ys

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
unshift x (y ∷ xs) = case x ≟ y of λ
  { (no _) → ⊥
  ; (yes _) → force xs
  }

_⋙_ : ST X Y → ST Y Z → ST X Z
f ⋙ g = g ∘ f

-- parallel composition
_⊗_ : ST X Y → ST Z W → ST (X × Z) (Y × W)
(f ⊗ g) xzs = zip (f (unzipₗ xzs)) (g (unzipᵣ xzs))

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST X Y
F-map-fold-aux : A → (A → X ⇌ Y) → (A → X → A) → ∞Colist⊥ X → Maybe Y → Colist⊥ Y
F-map-fold a f g [] = []
F-map-fold a f g ⊥ = ⊥
F-map-fold a f g (x ∷ xs) = F-map-fold-aux (g a x) f g xs (f a .to x)
F-map-fold-aux a f g xs nothing = ⊥
F-map-fold-aux a f g xs (just y) = y ∷ λ where .force → F-map-fold a f g (force xs)

F⟦_⟧ : E X Y → ST X Y
F⟦ `map-fold a f g ⟧ = F-map-fold a f g
F⟦ `delay x ⟧ = shift x
F⟦ `hasten x ⟧ = unshift x
F⟦ e `⋙ e' ⟧ = F⟦ e ⟧ ⋙ F⟦ e' ⟧
F⟦ e `⊗ e' ⟧ = F⟦ e ⟧ ⊗ F⟦ e' ⟧

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST Y X
B-map-fold-aux : A → (A → X ⇌ Y) → (A → X → A) → ∞Colist⊥ Y → Maybe X → Colist⊥ X
B-map-fold a f g [] = []
B-map-fold a f g ⊥ = ⊥
B-map-fold a f g (y ∷ ys) = B-map-fold-aux a f g ys (f a .from y)
B-map-fold-aux a f g ys nothing = ⊥
B-map-fold-aux a f g ys (just x) = x ∷ λ where .force → B-map-fold (g a x) f g (force ys)

B⟦_⟧ : E X Y → ST Y X
B⟦ `map-fold a f g ⟧ = B-map-fold a f g
B⟦ `delay x ⟧ = unshift x
B⟦ `hasten x ⟧ = shift x
B⟦ e `⋙ e' ⟧ = B⟦ e' ⟧ ⋙ B⟦ e ⟧
B⟦ e `⊗ e' ⟧ = B⟦ e ⟧ ⊗ B⟦ e' ⟧

--------------------------------------------------------------------------------

F-empty : ∀ (e : E X Y) → F⟦ e ⟧ [] ≡ []
F-empty (`map-fold a f g) = refl
F-empty (`delay x) = refl
F-empty (`hasten x) = refl
F-empty (e `⋙ e') = cong F⟦ e' ⟧ (F-empty e) ∙ F-empty e'
F-empty (e `⊗ e') = cong₂ zip (F-empty e) (F-empty e')

B-empty : ∀ (e : E X Y) → B⟦ e ⟧ [] ≡ []
B-empty (`map-fold a f g) = refl
B-empty (`delay x) = refl
B-empty (`hasten x) = refl
B-empty (e `⋙ e') = cong B⟦ e ⟧ (B-empty e') ∙ B-empty e
B-empty (e `⊗ e') = cong₂ zip (B-empty e) (B-empty e')

--------------------------------------------------------------------------------
-- Incrementality of F and B

prefix-cong-shift : ∀ (x : A) {xs' xs}
  → Prefix k xs' xs
  → Prefix k (shift x xs') (shift x xs)
prefix-cong-shift x {[]} {xs'} p = con tt
prefix-cong-shift {k = ⊥≺⊥} x {⊥} {[]} (con ())
prefix-cong-shift {k = ⊥≺⊥} x {⊥} {⊥} p = con tt
prefix-cong-shift {k = ⊥≺⊥} x {⊥} {_ ∷ _} (con ())
prefix-cong-shift {k = ⊥≺} x {⊥} {xs'} p = con tt
prefix-cong-shift x {_ ∷ _} {[]} (con ())
prefix-cong-shift x {_ ∷ _} {⊥} (con ())
prefix-cong-shift x {_ ∷ _} {_ ∷ _} (con (p , q)) rewrite pathToEq p =
  con (refl , λ where .force → prefix-cong-shift _ (force q))

prefix-cong-unshift : ∀ {{_ : Eq A}} (x : A) {xs' xs}
  → Prefix k xs' xs
  → Prefix k (unshift x xs') (unshift x xs)
prefix-cong-unshift x {[]} {xs} p = con tt
prefix-cong-unshift {k = ⊥≺⊥} x {⊥} {[]} (con ())
prefix-cong-unshift {k = ⊥≺⊥} x {⊥} {⊥} p = con tt
prefix-cong-unshift {k = ⊥≺⊥} x {⊥} {_ ∷ _} (con ())
prefix-cong-unshift {k = ⊥≺} x {⊥} {xs} p = con tt
prefix-cong-unshift x {_ ∷ _} {[]} (con ())
prefix-cong-unshift x {_ ∷ _} {⊥} (con ())
prefix-cong-unshift x {y ∷ _} {_ ∷ _} (con (p , q)) rewrite pathToEq (sym p) with x ≟ y
prefix-cong-unshift x {y ∷ _} {_ ∷ _} (con (p , q)) | yes _ = force q
prefix-cong-unshift {k = ⊥≺⊥} x {y ∷ _} {_ ∷ _} (con (p , q)) | no _ = con tt
prefix-cong-unshift {k = ⊥≺} x {y ∷ _} {_ ∷ _} (con (p , q)) | no _ = con tt

prefix-cong-⊗ : ∀ {f : ST X Y} {g : ST Z W}
  → (∀ {xs' xs} → Prefix k xs' xs → Prefix k (f xs') (f xs))
  → (∀ {xs' xs} → Prefix k xs' xs → Prefix k (g xs') (g xs))
  → (∀ {xzs' xzs} → Prefix k xzs' xzs → Prefix k ((f ⊗ g) xzs') ((f ⊗ g) xzs))
prefix-cong-⊗ p q r = prefix-cong-zip (p (prefix-cong-unzipₗ r)) (q (prefix-cong-unzipᵣ r))

prefix-cong-F : ∀ (e : E X Y) {xs' xs}
  → Prefix k xs' xs
  → Prefix k (F⟦ e ⟧ xs') (F⟦ e ⟧ xs)
prefix-cong-F (`map-fold a f g) = helper a
  where
    helper : ∀ a {xs' xs}
      → Prefix k xs' xs
      → Prefix k (F⟦ `map-fold a f g ⟧ xs') (F⟦ `map-fold a f g ⟧ xs)
    helper a {[]} {xs} p = con tt
    helper {k = ⊥≺⊥} a {⊥} {[]} (con ())
    helper {k = ⊥≺⊥} a {⊥} {⊥} p = con tt
    helper {k = ⊥≺⊥} a {⊥} {_ ∷ _} (con ())
    helper {k = ⊥≺} a {⊥} {xs} p = con tt
    helper a {_ ∷ _} {[]} (con ())
    helper a {_ ∷ _} {⊥} (con ())
    helper a {x ∷ _} {_ ∷ _} (con (p , q)) rewrite pathToEq (sym p) with f a .to x
    helper a {x ∷ _} {_ ∷ _} (con (p , q)) | just y = con (refl , λ where .force → helper (g a x) (force q))
    helper {k = ⊥≺⊥} a {_ ∷ _} {_ ∷ _} (con (p , q)) | nothing = con tt
    helper {k = ⊥≺} a {_ ∷ _} {_ ∷ _} (con (p , q)) | nothing = con tt
prefix-cong-F (`delay x) = prefix-cong-shift x
prefix-cong-F (`hasten x) = prefix-cong-unshift x
prefix-cong-F (e `⋙ e') = prefix-cong-F e' ∘ prefix-cong-F e
prefix-cong-F (e `⊗ e') = prefix-cong-⊗ (prefix-cong-F e) (prefix-cong-F e')

prefix-cong-B : ∀ (e : E X Y) {xs' xs}
  → Prefix k xs' xs
  → Prefix k (B⟦ e ⟧ xs') (B⟦ e ⟧ xs)
prefix-cong-B (`map-fold a f g) = helper a
  where
    helper : ∀ a {xs' xs}
      → Prefix k xs' xs
      → Prefix k (B⟦ `map-fold a f g ⟧ xs') (B⟦ `map-fold a f g ⟧ xs)
    helper a {[]} {xs} p = con tt
    helper {k = ⊥≺⊥} a {⊥} {[]} (con ())
    helper {k = ⊥≺⊥} a {⊥} {⊥} p = con tt
    helper {k = ⊥≺⊥} a {⊥} {_ ∷ _} (con ())
    helper {k = ⊥≺} a {⊥} {xs} p = con tt
    helper a {_ ∷ _} {[]} (con ())
    helper a {_ ∷ _} {⊥} (con ())
    helper a {y ∷ _} {_ ∷ _} (con (p , q)) rewrite pathToEq (sym p) with f a .from y
    helper a {y ∷ _} {_ ∷ _} (con (p , q)) | just x = con (refl , λ where .force → helper (g a x) (force q))
    helper {k = ⊥≺⊥} a {y ∷ _} {_ ∷ _} (con (p , q)) | nothing = con tt
    helper {k = ⊥≺} a {y ∷ _} {_ ∷ _} (con (p , q)) | nothing = con tt
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
  shift-hasDelay x [] = con tt
  shift-hasDelay x ⊥ = con tt
  shift-hasDelay x (y ∷ xs) = con λ where .force → shift-hasDelay y (force xs)

  unshift-hasDelay : ∀ {{_ : Eq A}} (x : A) → HasDelay 1 (unshift x)
  unshift-hasDelay x [] = con tt
  unshift-hasDelay x ⊥ = con tt
  unshift-hasDelay x (y ∷ xs) with x ≟ y
  ... | no _ = con tt
  ... | yes _ = ⊑-refl

  ∘-hasDelay : ∀ {f : ST Y Z} {g : ST X Y} d d'
    → HasDelay d f
    → HasDelay d' g
    → HasDelay (d' + d) (f ∘ g)
  ∘-hasDelay {f = f} {g} d d' p q xs = begin
    colength (f (g xs))      ≲⟨ p (g xs) ⟩
    colength (g xs) ∸ℕ d     ≲⟨ ⊑-cong-∸ℕ d (q xs) ⟩
    colength xs ∸ℕ d' ∸ℕ d   ≈⟨ ∸ℕ-+-assoc (colength xs) d' d ⟩
    colength xs ∸ℕ (d' + d)  ∎

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
    ≈⟨ cong₂ (λ m n → (m ∸ℕ d) ⊓ (n ∸ℕ d')) colength-unzipₗ colength-unzipᵣ ⟩
      (colength xzs ∸ℕ d) ⊓ (colength xzs ∸ℕ d')
    ≈⟨ sym (∸ℕ-distribˡ-⊔-⊓ (colength xzs) d d') ⟩
      colength xzs ∸ℕ (d ⊔ d')
    ∎

  F-hasDelay : ∀ (e : E X Y) → HasDelay DF⟦ e ⟧ F⟦ e ⟧
  F-hasDelay (`map-fold a f g) = helper a
    where
      helper : ∀ a → HasDelay 0 F⟦ `map-fold a f g ⟧
      helper a [] = con tt
      helper a ⊥ = con tt
      helper a (x ∷ xs) with f a .to x
      ... | nothing = con tt
      ... | just y = con λ where .force → helper (g a x) (force xs)
  F-hasDelay (`delay x) = shift-hasDelay x
  F-hasDelay (`hasten x) = unshift-hasDelay x
  F-hasDelay (e `⋙ e') = ∘-hasDelay DF⟦ e' ⟧ DF⟦ e ⟧ (F-hasDelay e') (F-hasDelay e)
  F-hasDelay (e `⊗ e') = ⊗-hasDelay DF⟦ e ⟧ DF⟦ e' ⟧ (F-hasDelay e) (F-hasDelay e')

  B-hasDelay : ∀ (e : E X Y) → HasDelay DB⟦ e ⟧ B⟦ e ⟧
  B-hasDelay (`map-fold a f g) = helper a
    where
      helper : ∀ a → HasDelay 0 B⟦ `map-fold a f g ⟧
      helper a [] = con tt
      helper a ⊥ = con tt
      helper a (y ∷ ys) with f a .from y
      ... | nothing = con tt
      ... | just x = con λ where .force → helper (g a x) (force ys)
  B-hasDelay (`delay x) = unshift-hasDelay x
  B-hasDelay (`hasten x) = shift-hasDelay x
  B-hasDelay (e `⋙ e') = ∘-hasDelay DB⟦ e ⟧ DB⟦ e' ⟧ (B-hasDelay e) (B-hasDelay e')
  B-hasDelay (e `⊗ e') = ⊗-hasDelay DB⟦ e ⟧ DB⟦ e' ⟧ (B-hasDelay e) (B-hasDelay e')

--------------------------------------------------------------------------------
-- F⟦_⟧ and B⟦_⟧ are inverse of each other

shift-≺≺-∷ : ∀ (x : A) xs → shift x xs ≺≺ x ∷ delay xs
shift-≺≺-∷ x [] = con tt
shift-≺≺-∷ x ⊥ = con tt
shift-≺≺-∷ x (y ∷ xs) = con (refl , λ where .force → shift-≺≺-∷ y (force xs))

shift-IIST : ∀ {{_ : Eq X}} (x : X) → shift x IsIISTOf unshift x
shift-IIST x [] = con tt
shift-IIST x ⊥ = con tt
shift-IIST x (y ∷ xs) with x ≟ y
... | no _ = con tt
... | yes eq rewrite pathToEq eq = shift-≺≺-∷ y (force xs)

unshift-IIST : ∀ {{_ : Eq X}} (x : X) → unshift x IsIISTOf shift x
unshift-IIST x [] = con tt
unshift-IIST x ⊥ = con tt
unshift-IIST x (y ∷ xs) with x ≟ x
... | no ¬refl = Empty.rec (¬refl refl)
... | yes _ = shift-≺≺-∷ y (force xs)

∘-IIST : ∀ {f : ST Y Z} {f' : ST Z Y} {g : ST X Y} {g' : ST Y X}
  → f IsIISTOf f'
  → g IsIISTOf g'
  → (∀ {xs' xs} → xs' ≺≺ xs → f xs' ≺≺ f xs)
  → (f ∘ g) IsIISTOf (g' ∘ f')
∘-IIST {f = f} {f'} {g} {g'} f-inv-f' g-inv-g' f-inc zs = begin
  f (g (g' (f' zs)))  ≲⟨ f-inc (g-inv-g' (f' zs)) ⟩
  f (f' zs)           ≲⟨ f-inv-f' zs ⟩
  zs                  ∎
  where open PrefixReasoning

⊗-IIST : ∀ {f : ST X Y} {f' : ST Y X} {g : ST Z W} {g' : ST W Z}
  → f IsIISTOf f'
  → g IsIISTOf g'
  → (∀ {xs' xs} → xs' ≺≺ xs → f xs' ≺≺ f xs)
  → (∀ {xs' xs} → xs' ≺≺ xs → g xs' ≺≺ g xs)
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
    helper a [] = con tt
    helper a ⊥ = con tt
    helper a (y ∷ ys) with f a .from y | inspect (f a .from) y
    ... | nothing | [ eq ]ᵢ = con tt
    ... | just x | [ eq ]ᵢ rewrite pathToEq (f a .from→to eq) =
          con (refl , λ where .force → helper (g a x) (force ys))
F-IIST (`delay x) = shift-IIST x
F-IIST (`hasten x) = unshift-IIST x
F-IIST (e `⋙ e') = ∘-IIST {g = F⟦ e ⟧} (F-IIST e') (F-IIST e) (prefix-cong-F e')
F-IIST (e `⊗ e') = ⊗-IIST (F-IIST e) (F-IIST e') (prefix-cong-F e) (prefix-cong-F e')

B-IIST : ∀ (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (`map-fold a f g) = helper a
  where
    helper : ∀ a → B⟦ `map-fold a f g ⟧ IsIISTOf F⟦ `map-fold a f g ⟧
    helper a [] = con tt
    helper a ⊥ = con tt
    helper a (x ∷ xs) with f a .to x | inspect (f a .to) x
    ... | nothing | [ eq ]ᵢ = con tt
    ... | just y | [ eq ]ᵢ rewrite pathToEq (f a .to→from eq) =
          con (refl , λ where .force → helper (g a x) (force xs))
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

F∘I≡B : ∀ (e : E X Y) → F⟦ I⟦ e ⟧ ⟧ ≡ B⟦ e ⟧
F∘I≡B (`map-fold a f g) = helper a
  where
    helper : ∀ a → F⟦ I⟦ `map-fold a f g ⟧ ⟧ ≡ B⟦ `map-fold a f g ⟧
    helper a i [] = []
    helper a i ⊥ = ⊥
    helper a i (y ∷ ys) with f a .from y
    ... | nothing = ⊥
    ... | just x = x ∷ λ where .force → helper (g a x) i (force ys)
F∘I≡B (`delay x) = refl
F∘I≡B (`hasten x) = refl
F∘I≡B (e `⋙ e') = cong₂ _⋙_ (F∘I≡B e') (F∘I≡B e)
F∘I≡B (e `⊗ e') = cong₂ _⊗_ (F∘I≡B e) (F∘I≡B e')

B∘I≡F : ∀ (e : E X Y) → B⟦ I⟦ e ⟧ ⟧ ≡ F⟦ e ⟧
B∘I≡F (`map-fold a f g) = helper {a} refl
  where
    helper : ∀ {a a'} → a ≡ a' → B⟦ I⟦ `map-fold a f g ⟧ ⟧ ≡ F⟦ `map-fold a' f g ⟧
    helper eq i [] = []
    helper eq i ⊥ = ⊥
    helper {a} eq i (x ∷ xs) rewrite pathToEq (sym eq) with f a .to x | inspect (f a .to) x
    ... | nothing | [ eq' ]ᵢ = ⊥
    ... | just y | [ eq' ]ᵢ = y ∷ λ where .force → helper (congS (Maybe.rec a (g a)) (f a .to→from eq')) i (force xs)
B∘I≡F (`delay x) = refl
B∘I≡F (`hasten x) = refl
B∘I≡F (e `⋙ e') = cong₂ _⋙_ (B∘I≡F e) (B∘I≡F e')
B∘I≡F (e `⊗ e') = cong₂ _⊗_ (B∘I≡F e) (B∘I≡F e')
