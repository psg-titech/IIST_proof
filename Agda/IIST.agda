-- Tested with agda 2.6.4 and agda-stdlib 1.7.3

module IIST where

open import Category.Monad using ( RawMonad )
open RawMonad {{...}} using ( _>>=_; return ) renaming ( _<=<_ to _∙_ )
open import Data.List using ( List; []; _∷_; zip; unzip; length )
open import Data.List.Properties using ( length-zipWith; zipWith-unzipWith )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Maybe.Categorical using ( monad )
open import Data.Maybe.Relation.Unary.All using ( All; just; nothing )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Nat using ( ℕ; zero; suc; _+_; _∸_; _⊔_ )
open import Data.Nat.Properties using ( +-comm; ∸-+-assoc; ∸-distribˡ-⊔-⊓ )
open import Data.Product using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
import Data.Product.Properties
open import Function using ( id; _$_ )
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

length-unzip : ∀ {xzs : List (X × Z)} {xs zs}
  → unzip xzs ≡ (xs , zs)
  → length xzs ≡ length xs × length xzs ≡ length zs
length-unzip {xzs = []} refl = refl , refl
length-unzip {xzs = (x , z) ∷ xzs} refl
  with xs , zs ← unzip xzs in eq
  with ih₁ , ih₂ ← length-unzip eq
  = cong suc ih₁ , cong suc ih₂

zip-unzip : ∀ {xzs : List (X × Z)} {xs zs}
  → unzip xzs ≡ (xs , zs)
  → zip xs zs ≡ xzs
zip-unzip {xzs = xzs} refl = zipWith-unzipWith id _,_ (λ _ → refl) xzs

-------------------------------------------------------------------------------
-- Partial function and Partial invertible function

_⇀_ : Set → Set → Set
X ⇀ Y = X → Maybe Y

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

instance

  eqNat : Eq ℕ
  _==_ {{eqNat}} = Data.Nat.Properties._≟_

  eqProd : {{_ : Eq X}} {{_ : Eq Y}} → Eq (X × Y)
  _==_ {{eqProd}} = Data.Product.Properties.≡-dec _==_ _==_

  eqList : {{_ : Eq X}} → Eq (List X)
  _==_ {{eqList}} = Data.List.Properties.≡-dec _==_

-------------------------------------------------------------------------------
-- List Prefix

-- xs' ⊆ xs : xs' is a prefix of xs
data _⊆_ {X : Set} : List X → List X → Set where
  [] : ∀ {xs} → [] ⊆ xs
  _∷_ : ∀ x {xs' xs} → xs' ⊆ xs → (x ∷ xs') ⊆ (x ∷ xs)

⊆-reflexive : ∀ (xs : List X) → xs ⊆ xs
⊆-reflexive [] = []
⊆-reflexive (x ∷ xs) = x ∷ ⊆-reflexive xs

⊆-trans : ∀ {xs ys zs : List X} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans [] _ = []
⊆-trans (x ∷ pf) (.x ∷ pf') = x ∷ ⊆-trans pf pf'

shift-⊆-∷ : ∀ (x : X) xs → shift x xs ⊆ (x ∷ xs)
shift-⊆-∷ x [] = []
shift-⊆-∷ x (x' ∷ xs) = x ∷ shift-⊆-∷ x' xs

⊆-shift : ∀ (x : X) {xs' xs} → xs' ⊆ xs → shift x xs' ⊆ shift x xs
⊆-shift x [] = []
⊆-shift x (x' ∷ pf) = x ∷ ⊆-shift x' pf

⊆-zip : ∀ {xs' xs : List X} {ys' ys : List Y}
  → xs' ⊆ xs
  → ys' ⊆ ys
  → zip xs' ys' ⊆ zip xs ys
⊆-zip [] _ = []
⊆-zip (_ ∷ _) [] = []
⊆-zip (x ∷ pf) (y ∷ pf') = (x , y) ∷ ⊆-zip pf pf'

⊆-unzip : ∀ {xys' xys : List (X × Y)} {xs' ys' xs ys}
  → xys' ⊆ xys
  → unzip xys' ≡ (xs' , ys')
  → unzip xys ≡ (xs , ys)
  → (xs' ⊆ xs) × (ys' ⊆ ys)
⊆-unzip [] refl refl = [] , []
⊆-unzip (_∷_ (x , y) {xs' = xys'} {xs = xys} pfxy) refl refl
  with xs' , ys' ← unzip xys' in eq'
  with xs , ys ← unzip xys in eq
  with pfx , pfy ← ⊆-unzip pfxy eq' eq =
    x ∷ pfx , y ∷ pfy

⊆-zip-unzip : ∀ {xs : List X} {ys : List Y} {xs' ys'}
  → unzip (zip xs ys) ≡ (xs' , ys')
  → (xs' ⊆ xs) × (ys' ⊆ ys)
⊆-zip-unzip {xs = []} refl = [] , []
⊆-zip-unzip {xs = x ∷ xs} {[]} refl = [] , []
⊆-zip-unzip {xs = x ∷ xs} {y ∷ ys} refl
  with xs' , ys' ← unzip (zip xs ys) in eq
  with pfx , pfy ← ⊆-zip-unzip eq
  = x ∷ pfx , y ∷ pfy

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
F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → List X ⇀ List Y
F-map-fold a f g [] = return []
F-map-fold a f g (x ∷ xs) = do
  y ← f a .to x
  ys ← F-map-fold (g a x) f g xs
  return $ y ∷ ys

F⟦_⟧_ : E X Y → List X ⇀ List Y
F⟦ map-fold a f g ⟧ xs = F-map-fold a f g xs
F⟦ delay x ⟧ xs = return $ shift x xs
F⟦ hasten x ⟧ [] = return []
F⟦ hasten x ⟧ (x' ∷ xs) with x == x'
... | no _ = nothing
... | yes refl = return xs
F⟦ e ⟫ e' ⟧ xs = F⟦ e' ⟧_  ∙ F⟦ e ⟧_ $ xs
F⟦ e ⊗ e' ⟧ xzs = do
  let xs , zs = unzip xzs
  ys ← F⟦ e ⟧ xs
  ws ← F⟦ e' ⟧ zs
  return $ zip ys ws


-- Backward semantics
B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → List Y ⇀ List X
B-map-fold a f g [] = just []
B-map-fold a f g (y ∷ ys) = do
  x ← f a .from y
  xs ← B-map-fold (g a x) f g ys
  return $ x ∷ xs

B⟦_⟧_ : E X Y → List Y ⇀ List X
B⟦ map-fold a f g ⟧ xs = B-map-fold a f g xs
B⟦ delay x ⟧ [] = return []
B⟦ delay x ⟧ (x' ∷ xs) with x == x'
... | no _ = nothing
... | yes refl = return xs
B⟦ hasten x ⟧ xs = return $ shift x xs
B⟦ e ⟫ e' ⟧ xs = B⟦ e ⟧_ ∙ B⟦ e' ⟧_ $ xs
B⟦ e ⊗ e' ⟧ yws = do
  let ys , ws = unzip yws
  xs ← B⟦ e ⟧ ys
  zs ← B⟦ e' ⟧ ws
  return $ zip xs zs


_ : F⟦ delay 0 ⟫ hasten 0 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ [])
_ = refl

_ : B⟦ delay 0 ⟫ hasten 0 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ [])
_ = refl

_ : F⟦ delay 0 ⟫ hasten 1 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ nothing
_ = refl

_ : F⟦ delay 0 ⊗ hasten 0 ⟧ ((1 , 0) ∷ (2 , 1) ∷ (3 , 2) ∷ (4 , 3) ∷ [])
    ≡ just ((0 , 1) ∷ (1 , 2) ∷ (2 , 3) ∷ [])
_ = refl

-------------------------------------------------------------------------------
-- Relations and Predicates

IsIST : (List X ⇀ List Y) → Set
IsIST f = ∀ {xs ys}
  → f xs ≡ just ys
  → ∀ {xs'} → xs' ⊆ xs
  → Σ[ ys' ∈ _ ] (ys' ⊆ ys) × (f xs' ≡ just ys')

Is-dST : ℕ → (List X ⇀ List Y) → Set
Is-dST d f = ∀ {xs ys}
  → f xs ≡ just ys
  → length ys ≡ length xs ∸ d

record Is-dIST (d : ℕ) (f : List X ⇀ List Y) : Set where
  field
    isIST : IsIST f
    is-dST : Is-dST d f

open Is-dIST

IsIIST : (List X ⇀ List Y) → (List Y ⇀ List X) → Set
IsIIST f g = ∀ {xs ys}
  → f xs ≡ just ys
  → Σ[ xs' ∈ _ ] (xs' ⊆ xs) × (g ys ≡ just xs')

record Is-dIIST (d : ℕ) (to : List X ⇀ List Y) (from : List Y ⇀ List X) : Set where
  field
    to-is-dIST : Is-dIST d to
    from-is-IST : IsIST from
    isIIST : IsIIST to from

open Is-dIIST

-------------------------------------------------------------------------------
-- Properties of The Forward and Backward Semantics

F-IST : ∀ (e : E X Y) → IsIST F⟦ e ⟧_
F-IST (map-fold {A} a f g) = ind a
  where
    ind : (a : A) → IsIST F⟦ map-fold a f g ⟧_
    ind a eq [] = [] , [] , refl
    ind a eq (_∷_ x {xs = xs} pf)
      with just y ← f a .to x
      with just ys ← F-map-fold (g a x) f g xs in eq₁
      with ys' , pf' , eq₂ ← ind (g a x) eq₁ pf
      rewrite sym (just-injective eq) | eq₂ =
        y ∷ ys' , y ∷ pf' , refl
F-IST (delay x) refl {xs'} pf = shift x xs' , ⊆-shift x pf , refl
F-IST (hasten x) _ [] = [] , [] , refl
F-IST (hasten x) eq (_∷_ x' {xs' = xs'} pf)
  with yes refl ← x == x'
  rewrite just-injective eq =
    xs' , pf , refl
F-IST (e ⟫ e') {xs} eq {xs'} pfx
  with just ys ← F⟦ e ⟧ xs in eq₁
  with ys' , pfy , eq₂ ← F-IST e eq₁ pfx
  with just zs ← F⟦ e' ⟧ ys in eq₃
  with zs' , pfz , eq₄ ← F-IST e' eq₃ pfy
  rewrite sym (just-injective eq) | eq₂ | eq₄ =
    zs' , pfz , refl
F-IST (e ⊗ e') {xzs} eq {xzs'} pfxz
  with xs' , zs' ← unzip xzs' in eq₁
  with xs , zs ← unzip xzs in eq₂
  with pfx , pfz ← ⊆-unzip pfxz eq₁ eq₂
  with just ys ← F⟦ e ⟧ xs in eq₃
  with just ws ← F⟦ e' ⟧ zs in eq₄
  with ys' , pfy , eq₅ ← F-IST e eq₃ pfx
  with ws' , pfw , eq₆ ← F-IST e' eq₄ pfz
  rewrite sym (just-injective eq) | eq₅ | eq₆ =
    zip ys' ws' , ⊆-zip pfy pfw , refl


B-IST : ∀ (e : E X Y) → IsIST B⟦ e ⟧_
B-IST (map-fold {A} a f g) = ind a
  where
    ind : (a : A) → IsIST B⟦ map-fold a f g ⟧_
    ind a eq [] = [] , [] , refl
    ind a eq (_∷_ y {xs = ys} pf)
      with just x ← f a .from y
      with just xs ← B-map-fold (g a x) f g ys in eq₁
      with xs' , pf' , eq₂ ← ind (g a x) eq₁ pf
      rewrite sym (just-injective eq) | eq₂ =
        x ∷ xs' , x ∷ pf' , refl
B-IST (delay x) _ [] = [] , [] ,  refl
B-IST (delay x) eq (_∷_ x' {xs' = xs} pf)
  with yes refl ← x == x'
  rewrite just-injective eq =
    xs , pf , refl
B-IST (hasten x) refl {xs'} pf = shift x xs' , ⊆-shift x pf , refl
B-IST (e ⟫ e') {zs} eq {zs'} pfz
  with just ys ← B⟦ e' ⟧ zs in eq₁
  with ys' , pfy , eq₂ ← B-IST e' eq₁ pfz
  with just xs ← B⟦ e ⟧ ys in eq₃
  with xs' , pfx , eq₄ ← B-IST e eq₃ pfy
  rewrite sym (just-injective eq) | eq₂ | eq₄ =
    xs' , pfx , refl
B-IST (e ⊗ e') {yws} eq {yws'} pfyw
  with ys' , ws' ← unzip yws' in eq₁
  with ys , ws ← unzip yws in eq₂
  with pfy , pfw ← ⊆-unzip pfyw eq₁ eq₂
  with just xs ← B⟦ e ⟧ ys in eq₃
  with just zs ← B⟦ e' ⟧ ws in eq₄
  with xs' , pfx , eq₅ ← B-IST e eq₃ pfy
  with zs' , pfz , eq₆ ← B-IST e' eq₄ pfw
  rewrite sym (just-injective eq) | eq₅ | eq₆ =
    zip xs' zs' , ⊆-zip pfx pfz , refl


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
dB⟦ e ⟫ e' ⟧ = dB⟦ e ⟧ + dB⟦ e' ⟧
dB⟦ e ⊗ e' ⟧ = dB⟦ e ⟧ ⊔ dB⟦ e' ⟧


F-dST : ∀ (e : E X Y) → Is-dST dF⟦ e ⟧ F⟦ e ⟧_
F-dST (map-fold {A} a f g) {xs} = ind a {xs}
  where
    ind : (a : A) → Is-dST 0 F⟦ map-fold a f g ⟧_
    ind a {[]} refl = refl
    ind a {x ∷ xs} eq
      with just y ← f a .to x | just ys ← F-map-fold (g a x) f g xs in eq₁
      with ih ← ind (g a x) {xs} eq₁
      rewrite sym (just-injective eq) =
        cong suc ih
F-dST (delay x) {xs} refl = shift-length x xs
F-dST (hasten x) {[]} refl = refl
F-dST (hasten x) {x' ∷ xs} eq
  with yes refl ← x == x'
  rewrite sym (just-injective eq) =
    refl
F-dST (e ⟫ e') {xs} eq
  with just ys ← F⟦ e ⟧ xs in eq₁
  with ih₁ ← F-dST e eq₁
  with just zs ← F⟦ e' ⟧ ys in eq₂
  with ih₂ ← F-dST e' eq₂
  rewrite sym (just-injective eq) | ih₁ | ih₂ =
    ∸-+-assoc (length xs) dF⟦ e ⟧ dF⟦ e' ⟧
F-dST (e ⊗ e') {xzs} eq
  with xs , zs ← unzip xzs in eq₁
  with just ys ← F⟦ e ⟧ xs in eq₂ | just ws ← F⟦ e' ⟧ zs in eq₃
  with ih₁ ← F-dST e eq₂ | ih₂ ← F-dST e' eq₃
  rewrite sym (just-injective eq) | length-zipWith _,_ ys ws | ih₁ | ih₂
  with eq₄ , eq₅ ← length-unzip eq₁
  rewrite sym eq₄ | sym eq₅ =
    sym (∸-distribˡ-⊔-⊓ (length xzs) dF⟦ e ⟧ dF⟦ e' ⟧)

B-dST : ∀ (e : E X Y) → Is-dST dB⟦ e ⟧ B⟦ e ⟧_
B-dST (map-fold {A} a f g) {ys} = ind a {ys}
  where
    ind : (a : A) → Is-dST 0 B⟦ map-fold a f g ⟧_
    ind a {[]} refl = refl
    ind a {y ∷ ys} eq
      with just x ← f a .from y
      with just xs ← B-map-fold (g a x) f g ys in eq₁
      with ih ← ind (g a x) {ys} eq₁
      rewrite sym (just-injective eq) =
        cong suc ih
B-dST (delay x) {[]} refl = refl
B-dST (delay x) {x' ∷ xs} eq
  with yes refl ← x == x'
  rewrite sym (just-injective eq) =
    refl
B-dST (hasten x) {xs} refl = shift-length x xs
B-dST (e ⟫ e') {zs} eq
  with just ys ← B⟦ e' ⟧ zs in eq₁
  with ih₁ ← B-dST e' eq₁
  with just xs ← B⟦ e ⟧ ys in eq₂
  with ih₂ ← B-dST e eq₂
  rewrite sym (just-injective eq) | ih₁ | ih₂
  rewrite ∸-+-assoc (length zs) dB⟦ e' ⟧ dB⟦ e ⟧ =
    cong (length zs ∸_) (+-comm dB⟦ e' ⟧ dB⟦ e ⟧)
B-dST (e ⊗ e') {yws} eq
  with ys , ws ← unzip yws in eq₁
  with just xs ← B⟦ e ⟧ ys in eq₂ | just zs ← B⟦ e' ⟧ ws in eq₃
  with ih₁ ← B-dST e eq₂ | ih₂ ← B-dST e' eq₃
  rewrite sym (just-injective eq) | length-zipWith _,_ xs zs | ih₁ | ih₂
  with eq₄ , eq₅ ← length-unzip eq₁
  rewrite sym eq₄ | sym eq₅ =
    sym (∸-distribˡ-⊔-⊓ (length yws) dB⟦ e ⟧ dB⟦ e' ⟧)


F-IIST : ∀ (e : E X Y) → IsIIST F⟦ e ⟧_ B⟦ e ⟧_
F-IIST (map-fold {A = A} a f g) = ind a
  where
    ind : (a : A) → IsIIST F⟦ map-fold a f g ⟧_ B⟦ map-fold a f g ⟧_
    ind a {[]} refl = [] , [] , refl
    ind a {x ∷ xs} eq
      with just y ← f a .to x in eq₁
      with just ys ← F-map-fold (g a x) f g xs in eq₂
      rewrite sym (just-injective eq)
      with just .x ← f a .from y | refl ← f a .invertible .proj₁ eq₁
      with xs' , pf , eq₃ ← ind (g a x) {xs} eq₂
      rewrite eq₃ =
        x ∷ xs' , x ∷ pf , refl
F-IIST (delay x) {[]} refl = [] , [] , refl
F-IIST (delay x) {x' ∷ xs} refl with x == x
... | no contra with () ← contra refl
... | yes refl = shift x' xs , shift-⊆-∷ x' xs , refl
F-IIST (hasten x) {[]} refl = [] , [] , refl
F-IIST (hasten x) {x' ∷ xs} eq
  with yes refl ← x == x'
  rewrite sym (just-injective eq) =
    shift x' xs , shift-⊆-∷ x xs , refl
F-IIST (e ⟫ e') {xs} {zs} eq
  with just ys ← F⟦ e ⟧ xs in eq₁
  with xs' , pfx , eq₁ ← F-IIST e eq₁
  with just zs ← F⟦ e' ⟧ ys in eq₂
  with ys' , pfy , eq₂ ← F-IIST e' eq₂
  with xs'' , pfx' , eq₃ ← B-IST e eq₁ pfy
  rewrite sym (just-injective eq) | eq₁ | eq₂
  = xs'' , ⊆-trans pfx' pfx , eq₃
F-IIST (e ⊗ e') {xzs} eq
  with xs , zs ← unzip xzs in eq₁
  with just ys ← F⟦ e ⟧ xs in eq₂
  with just ws ← F⟦ e' ⟧ zs in eq₃
  with xs' , pfx , eq₂ ← F-IIST e eq₂
  with zs' , pfz , eq₃ ← F-IIST e' eq₃
  rewrite sym (just-injective eq)
  with ys' , ws' ← unzip (zip ys ws) in eq₄
  with pfy , pfw ← ⊆-zip-unzip eq₄
  rewrite eq₄
  with xs'' , pfx' , eq₅ ← B-IST e eq₂ pfy
  with zs'' , pfz' , eq₆ ← B-IST e' eq₃ pfw
  rewrite sym (zip-unzip eq₁) | eq₅ | eq₆
  = zip xs'' zs'' , ⊆-zip (⊆-trans pfx' pfx) (⊆-trans pfz' pfz) , refl

B-IIST : ∀ (e : E X Y) → IsIIST B⟦ e ⟧_ F⟦ e ⟧_
B-IIST (map-fold {A = A} a f g) = ind a
  where
    ind : (a : A) → IsIIST B⟦ map-fold a f g ⟧_ F⟦ map-fold a f g ⟧_
    ind a {[]} refl = [] , [] , refl
    ind a {y ∷ ys} eq
      with just x ← f a .from y in eq₁
      with just xs ← B-map-fold (g a x) f g ys in eq₂
      rewrite sym (just-injective eq)
      with just .y ← f a .to x | refl ← f a .invertible .proj₂ eq₁
      with ys' , pf , eq₃ ← ind (g a x) {ys} eq₂
      rewrite eq₃ =
        y ∷ ys' , y ∷ pf , refl
B-IIST (delay x) {[]} refl = [] , [] , refl
B-IIST (delay x) {x' ∷ xs} eq
  with yes refl ← x == x'
  rewrite sym (just-injective eq) =
    shift x' xs , shift-⊆-∷ x xs , refl
B-IIST (hasten x) {[]} refl = [] , [] , refl
B-IIST (hasten x) {x' ∷ xs} refl with x == x
... | no contra with () ← contra refl
... | yes refl = shift x' xs , shift-⊆-∷ x' xs , refl
B-IIST (e ⟫ e') {zs} {xs} eq
  with just ys ← B⟦ e' ⟧ zs in eq₁
  with zs' , pfz , eq₁ ← B-IIST e' eq₁
  with just xs ← B⟦ e ⟧ ys in eq₂
  with ys' , pfy , eq₂ ← B-IIST e eq₂
  with zs'' , pfz' , eq₃ ← F-IST e' eq₁ pfy
  rewrite sym (just-injective eq) | eq₁ | eq₂
  = zs'' , ⊆-trans pfz' pfz , eq₃
B-IIST (e ⊗ e') {yws} eq
  with ys , ws ← unzip yws in eq₁
  with just xs ← B⟦ e ⟧ ys in eq₂
  with just zs ← B⟦ e' ⟧ ws in eq₃
  with ys' , pfy , eq₂ ← B-IIST e eq₂
  with ws' , pfw , eq₃ ← B-IIST e' eq₃
  rewrite sym (just-injective eq)
  with xs' , zs' ← unzip (zip xs zs) in eq₄
  with pfx , pfz ← ⊆-zip-unzip eq₄
  rewrite eq₄
  with ys'' , pfy' , eq₅ ← F-IST e eq₂ pfx
  with ws'' , pfw' , eq₆ ← F-IST e' eq₃ pfz
  rewrite sym (zip-unzip eq₁) | eq₅ | eq₆
  = zip ys'' ws'' , ⊆-zip (⊆-trans pfy' pfy) (⊆-trans pfw' pfw) , refl


F-dIIST : ∀ (e : E X Y) → Is-dIIST dF⟦ e ⟧ F⟦ e ⟧_ B⟦ e ⟧_
F-dIIST e .to-is-dIST .isIST = F-IST e
F-dIIST e .to-is-dIST .is-dST = F-dST e
F-dIIST e .from-is-IST = B-IST e
F-dIIST e .isIIST = F-IIST e

B-dIIST : ∀ (e : E X Y) → Is-dIIST dB⟦ e ⟧ B⟦ e ⟧_ F⟦ e ⟧_
B-dIIST e .to-is-dIST .isIST = B-IST e
B-dIIST e .to-is-dIST .is-dST = B-dST e
B-dIIST e .from-is-IST = F-IST e
B-dIIST e .isIIST = B-IIST e
