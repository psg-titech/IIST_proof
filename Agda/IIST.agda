-- Tested with agda 2.6.4 and agda-stdlib 1.7.3

module IIST where

open import Category.Monad using ( RawMonad )
open RawMonad {{...}} using ( _>>=_; return ) renaming ( _<=<_ to _∙_ )
open import Data.List using ( List; []; _∷_; zip; unzip; length )
import Data.List.Properties
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Maybe.Categorical using ( monad )
open import Data.Maybe.Relation.Unary.All using ( All; just; nothing )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Nat using ( ℕ; zero; suc; _+_; _∸_; _⊔_ )
import Data.Nat.Properties
open import Data.Product using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
import Data.Product.Properties
open import Function using ( _$_ )
open import Relation.Nullary using ( Dec; yes; no )
open import Relation.Binary.PropositionalEquality

infix 0 _⇀_ _⇌_ _↔_ _$?_
infixr 9 _⟫_
infixr 3 _⊗_

instance
  maybeMonad = monad

private
  variable
    A X Y Z W : Set

-------------------------------------------------------------------------------
-- Misc.

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (Q → P)

shift : X → List X → List X
shift _ [] = []
shift x (y ∷ xs) = x ∷ shift y xs

_ : shift 0 (1 ∷ 2 ∷ 3 ∷ []) ≡ 0 ∷ 1 ∷ 2 ∷ []
_ = refl

shift-length : ∀ (x : X) xs → length (shift x xs) ≡ length xs
shift-length x [] = refl
shift-length x (y ∷ xs) = cong suc (shift-length y xs)

_$?_ : (X → Set) → (Maybe X → Set)
_$?_ = All

-------------------------------------------------------------------------------
-- Partial function and Partial invertible function

_⇀_ : Set → Set → Set
X ⇀ Y = X → Maybe Y

record _⇌_ (X Y : Set) : Set where
  field
    to : X ⇀ Y
    from : Y ⇀ X
    invertible : ∀ x y → to x ≡ just y ↔ from y ≡ just x

open _⇌_

-------------------------------------------------------------------------------
-- Eq typeclass

record Eq (A : Set) : Set where
  infix 4 _==_
  field
    _==_ : (x y : A) → Dec (x ≡ y)

open Eq {{...}}

instance

  eqNat : Eq ℕ
  _==_ {{eqNat}} = Data.Nat.Properties._≟_

  eqProd : {{_ : Eq X}} {{_ : Eq Y}} → Eq (X × Y)
  _==_ {{eqProd}} = Data.Product.Properties.≡-dec _==_ _==_

  eqList : {{_ : Eq X}} → Eq (List X)
  _==_ {{eqList}} = Data.List.Properties.≡-dec _==_

-------------------------------------------------------------------------------
-- Syntax

data E : Set → Set → Set₁ where
  map-fold : A → (A → X ⇌ Y) → (A → X → A) → E X Y
  delay : {{_ : Eq X}} → X → E X X
  hasten : {{_ : Eq X}} → X → E X X
  _⟫_ : E X Y → E Y Z → E X Z
  _⊗_ : E X Y → E Z W → E (X × Z) (Y × W)

-------------------------------------------------------------------------------
-- Semantics

-- Forward semantics
F⟦_⟧_ : E X Y → List X ⇀ List Y
F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → List X ⇀ List Y

F⟦ map-fold a f g ⟧ xs = F-map-fold a f g xs
F⟦ delay x ⟧ xs = return $ shift x xs
F⟦ hasten x ⟧ [] = return []
F⟦ hasten x ⟧ (x' ∷ xs) with x == x'
... | no _ = nothing
... | yes refl = return xs
F⟦ e ⟫ e' ⟧ xs = F⟦ e' ⟧_  ∙ F⟦ e ⟧_ $ xs
F⟦ e ⊗ e' ⟧ xzs with xs , zs ← unzip xzs = do
  ys ← F⟦ e ⟧ xs
  ws ← F⟦ e' ⟧ zs
  return $ zip ys ws

F-map-fold a f g [] = return []
F-map-fold a f g (x ∷ xs) = do
  y ← f a .to x
  ys ← F-map-fold (g a x) f g xs
  return $ y ∷ ys


-- Backward semantics
B⟦_⟧_ : E X Y → List Y ⇀ List X
B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → List Y ⇀ List X

B⟦ map-fold a f g ⟧ xs = B-map-fold a f g xs
B⟦ delay x ⟧ [] = return []
B⟦ delay x ⟧ (x' ∷ xs) with x == x'
... | no _ = nothing
... | yes refl = return xs
B⟦ hasten x ⟧ xs = return $ shift x xs
B⟦ e ⟫ e' ⟧ xs = B⟦ e ⟧_ ∙ B⟦ e' ⟧_ $ xs
B⟦ e ⊗ e' ⟧ yws with ys , ws ← unzip yws = do
  xs ← B⟦ e ⟧ ys
  zs ← B⟦ e' ⟧ ws
  return $ zip xs zs

B-map-fold a f g [] = just []
B-map-fold a f g (y ∷ ys) = do
  x ← f a .from y
  xs ← B-map-fold (g a x) f g ys
  return $ x ∷ xs

-------------------------------------------------------------------------------
-- Relations and Predicates

-- xs' ⊆ xs : xs' is a prefix of xs
data _⊆_ {X : Set} : List X → List X → Set where
  [] : ∀ {xs} → [] ⊆ xs
  _∷_ : ∀ x {xs' xs} → xs' ⊆ xs → (x ∷ xs') ⊆ (x ∷ xs)

⊆-reflexive : ∀ (xs : List X) → xs ⊆ xs
⊆-reflexive [] = []
⊆-reflexive (x ∷ xs) = x ∷ ⊆-reflexive xs

⊆-trans : ∀ {xs ys zs : List X} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans [] _ = []
⊆-trans (x ∷ pfx) (.x ∷ pfx') = x ∷ ⊆-trans pfx pfx'

shift-⊆-∷ : ∀ (x : X) xs → shift x xs ⊆ (x ∷ xs)
shift-⊆-∷ x [] = []
shift-⊆-∷ x (x' ∷ xs) = x ∷ shift-⊆-∷ x' xs

⊆-shift : ∀ (x : X) {xs' xs} → xs' ⊆ xs → shift x xs' ⊆ shift x xs
⊆-shift x [] = []
⊆-shift x (x' ∷ pfx) = x ∷ ⊆-shift x' pfx

⊆-zip : ∀ {xs' xs : List X} {ys' ys : List Y}
  → xs' ⊆ xs
  → ys' ⊆ ys
  → zip xs' ys' ⊆ zip xs ys
⊆-zip [] _ = []
⊆-zip (_ ∷ _) [] = []
⊆-zip (x ∷ pfx) (y ∷ pfx') = (x , y) ∷ ⊆-zip pfx pfx'

⊆-unzip : ∀ {xys' xys : List (X × Y)} {xs' ys' xs ys}
  → xys' ⊆ xys
  → unzip xys' ≡ (xs' , ys')
  → unzip xys ≡ (xs , ys)
  → (xs' ⊆ xs) × (ys' ⊆ ys)
⊆-unzip [] refl refl = [] , []
⊆-unzip (_∷_ (x , y) {xs' = xys'} {xs = xys} pfxxy) refl refl
  with xs' , ys' ← unzip xys' in eq'
  with xs , ys ← unzip xys in eq
  with pfxx , pfxy ← ⊆-unzip pfxxy eq' eq =
    x ∷ pfxx , y ∷ pfxy

DropLast : ℕ → List X → List X → Set
DropLast d xs xs' = xs' ⊆ xs × length xs ∸ d ≡ length xs'

_ : DropLast 2 (0 ∷ 1 ∷ 2 ∷ []) (0 ∷ [])
_ = (0 ∷ []) , refl

_ : DropLast 5 (0 ∷ 1 ∷ 2 ∷ []) []
_ = [] , refl

IsIncremental : (List X ⇀ List Y) → Set
IsIncremental f = ∀ {xs ys}
  → f xs ≡ just ys
  → ∀ {xs'} → xs' ⊆ xs
  → Σ[ ys' ∈ _ ] (ys' ⊆ ys) × (f xs' ≡ just ys')

-------------------------------------------------------------------------------
-- Properties of The Forward and Backward Semantics

F-Incremental : ∀ (e : E X Y) → IsIncremental F⟦ e ⟧_
F-Incremental (map-fold {A} a f g) = ind a
  where
    ind : (a : A) → IsIncremental F⟦ map-fold a f g ⟧_
    ind a eq [] = [] , [] , refl
    ind a eq (_∷_ x {xs = xs} pfx)
      with just y ← f a .to x
      with just ys ← F⟦ map-fold (g a x) f g ⟧ xs in eq₁
      with ys' , pfx' , eq₂ ← ind (g a x) eq₁ pfx
      rewrite sym (just-injective eq) | eq₂ =
        y ∷ ys' , y ∷ pfx' , refl
F-Incremental (delay x) refl {xs'} pfx = shift x xs' , ⊆-shift x pfx , refl
F-Incremental (hasten x) _ [] = [] , [] , refl
F-Incremental (hasten x) eq (_∷_ x' {xs' = xs'} pfx)
  with yes refl ← x == x'
  rewrite just-injective eq =
    xs' , pfx , refl
F-Incremental (e ⟫ e') {xs} eq {xs'} pfxx
  with just ys ← F⟦ e ⟧ xs in eq₁
  with ys' , pfxy , eq₂ ← F-Incremental e eq₁ pfxx
  with just zs ← F⟦ e' ⟧ ys in eq₃
  with zs' , pfxz , eq₄ ← F-Incremental e' eq₃ pfxy
  rewrite sym (just-injective eq) | eq₂ | eq₄ =
    zs' , pfxz , refl
F-Incremental (e ⊗ e') {xzs} eq {xzs'} pfxxz
  with xs' , zs' ← unzip xzs' in eq₁
  with xs , zs ← unzip xzs in eq₂
  with pfxx , pfxz ← ⊆-unzip pfxxz eq₁ eq₂
  with just ys ← F⟦ e ⟧ xs in eq₃
  with just ws ← F⟦ e' ⟧ zs in eq₄
  with ys' , pfxy , eq₅ ← F-Incremental e eq₃ pfxx
  with ws' , pfxw , eq₆ ← F-Incremental e' eq₄ pfxz
  rewrite sym (just-injective eq) | eq₅ | eq₆ =
    zip ys' ws' , ⊆-zip pfxy pfxw , refl


B-Incremental : ∀ (e : E X Y) → IsIncremental B⟦ e ⟧_
B-Incremental (map-fold {A} a f g) = ind a
  where
    ind : (a : A) → IsIncremental B⟦ map-fold a f g ⟧_
    ind a eq [] = [] , [] , refl
    ind a eq (_∷_ y {xs = ys} pfx)
      with just x ← f a .from y
      with just xs ← B⟦ map-fold (g a x) f g ⟧ ys in eq₁
      with xs' , pfx' , eq₂ ← ind (g a x) eq₁ pfx
      rewrite sym (just-injective eq) | eq₂ =
        x ∷ xs' , x ∷ pfx' , refl
B-Incremental (delay x) _ [] = [] , [] ,  refl
B-Incremental (delay x) eq (_∷_ x' {xs' = xs} pfx)
  with yes refl ← x == x'
  rewrite just-injective eq =
    xs , pfx , refl
B-Incremental (hasten x) refl {xs'} pfx = shift x xs' , ⊆-shift x pfx , refl
B-Incremental (e ⟫ e') {zs} eq {zs'} pfxz
  with just ys ← B⟦ e' ⟧ zs in eq₁
  with ys' , pfxy , eq₂ ← B-Incremental e' eq₁ pfxz
  with just xs ← B⟦ e ⟧ ys in eq₃
  with xs' , pfxx , eq₄ ← B-Incremental e eq₃ pfxy
  rewrite sym (just-injective eq) | eq₂ | eq₄ =
    xs' , pfxx , refl
B-Incremental (e ⊗ e') {yws} eq {yws'} pfxyw
    with ys' , ws' ← unzip yws' in eq₁
    with ys , ws ← unzip yws in eq₂
    with pfxy , pfxw ← ⊆-unzip pfxyw eq₁ eq₂
    with just xs ← B⟦ e ⟧ ys in eq₃
    with just zs ← B⟦ e' ⟧ ws in eq₄
    with xs' , pfxx , eq₅ ← B-Incremental e eq₃ pfxy
    with zs' , pfxz , eq₆ ← B-Incremental e' eq₄ pfxw
    rewrite sym (just-injective eq) | eq₅ | eq₆ =
      zip xs' zs' , ⊆-zip pfxx pfxz , refl


dF⟦_⟧ : E X Y → ℕ
dF⟦ map-fold a f g ⟧ = 0
dF⟦ delay x ⟧ = 0
dF⟦ hasten x ⟧ = 1
dF⟦ e ⟫ e' ⟧ = dF⟦ e ⟧ + dF⟦ e' ⟧
dF⟦ e ⊗ e' ⟧ = dF⟦ e ⟧ ⊔ dF⟦ e' ⟧

dB⟦_⟧ : E X Y → ℕ
dB⟦ map-fold a f g ⟧ = 0
dB⟦ delay x ⟧ = 1
dB⟦ hasten x ⟧ = 0
dB⟦ e ⟫ e' ⟧ = dB⟦ e ⟧ + dB⟦ e ⟧
dB⟦ e ⊗ e' ⟧ = dB⟦ e ⟧ ⊔ dB⟦ e' ⟧

B∙F⟦_⟧_ : E X Y → List X ⇀ List X
B∙F⟦_⟧_ e = B⟦ e ⟧_ ∙ F⟦ e ⟧_

F∙B⟦_⟧_ : E X Y → List Y ⇀ List Y
F∙B⟦_⟧_ e = F⟦ e ⟧_ ∙ B⟦ e ⟧_

mutual

  B∙F : ∀ (e : E X Y) xs
    → DropLast (dF⟦ e ⟧ + dB⟦ e ⟧) xs $? B∙F⟦ e ⟧ xs
  B∙F (map-fold {A} a f g) = ind a
    where
      ind : ∀ (a : A) xs → DropLast 0 xs $? B∙F⟦ map-fold a f g ⟧ xs
      ind a [] = just ([] , refl)
      ind a (x ∷ xs) with f a .to x in eq
      ... | nothing = nothing
      ... | just y with F-map-fold (g a x) f g xs in eq₁
      ...   | nothing = nothing
      ...   | just ys with f a .from y | f a .invertible x y .proj₁ eq
      ...     | just .x | refl with B-map-fold (g a x) f g ys in eq₂
      ...       | nothing = nothing
      ...       | just xs' with ind (g a x) xs
      ...         | ih rewrite eq₁ | eq₂ with ih
      ...           | just (pfx , len-eq) = just (x ∷ pfx , cong suc len-eq)
  B∙F (delay x) [] = just ([] , refl)
  B∙F (delay x) (x' ∷ xs) with x == x
  ... | no _ = nothing
  ... | yes refl = just (shift-⊆-∷ x' xs , sym (shift-length x' xs))
  B∙F (hasten x) [] = just ([] , refl)
  B∙F (hasten x) (x' ∷ xs) with x == x'
  ... | no _ = nothing
  ... | yes refl = just (shift-⊆-∷ x xs , sym (shift-length x xs))
  B∙F (e ⟫ e') = {!   !}
  B∙F (e ⊗ e') = {!   !}

-------------------------------------------------------------------------------
-- Examples

_ : F⟦ delay 0 ⟫ hasten 0 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ [])
_ = refl

_ : B⟦ delay 0 ⟫ hasten 0 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ [])
_ = refl

_ : F⟦ delay 0 ⟫ hasten 1 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ nothing
_ = refl

_ :
  F⟦ delay 0 ⊗ hasten 0 ⟧ ((1 , 0) ∷ (2 , 1) ∷ (3 , 2) ∷ (4 , 3) ∷ []) ≡
  just ((0 , 1) ∷ (1 , 2) ∷ (2 , 3) ∷ [])
_ = refl
