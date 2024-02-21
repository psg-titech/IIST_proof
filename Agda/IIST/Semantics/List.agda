module IIST.Semantics.List where

open import Level using ( 0ℓ )
open import Data.List.Base using ( List; []; _∷_; zip; unzip; length )
open import Data.List.Properties using ( length-zipWith; length-unzipWith₁; length-unzipWith₂; zipWith-unzipWith )
open import Data.Maybe.Base using ( Maybe; just; nothing; maybe; _>>=_ )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Maybe.Effectful using () renaming ( monad to monadMaybe )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _∸_; _⊔_ )
open import Data.Nat.Instances
open import Data.Nat.Properties using ( +-comm; ∸-+-assoc; ∸-distribˡ-⊔-⊓; suc-injective )
open import Data.Product.Base using ( Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂ )
open import Effect.Monad using ( RawMonad )
open import Function using ( id; _∘_ )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.Core using ( _=[_]⇒_; _Preserves₂_⟶_⟶_ )
open import Relation.Binary.PropositionalEquality.Core

open import IIST.Common
open import IIST.Syntax

open RawMonad {0ℓ} monadMaybe using ( _>=>_; _<$>_; _<*>_; pure )

private
  variable
    A X Y Z W : Set

-------------------------------------------------------------------------------
-- Additional functions and relations on lists

infix 4 _≺_

shift : X → List X → List X
shift _ [] = []
shift x (y ∷ xs) = x ∷ shift y xs

unshift : {{_ : Eq X}} → X → List X ⇀ List X
unshift x [] = just []
unshift x (x' ∷ xs) with x ≟ x'
... | yes _ = just xs
... | no _ = nothing

zip-unzip : ∀ (xys : List (X × Y)) → zip (proj₁ (unzip xys)) (proj₂ (unzip xys)) ≡ xys
zip-unzip  = zipWith-unzipWith id _,_ (λ _ → refl)

-- xs' ≺ xs : xs' is a prefix of xs
data _≺_ {X} : List X → List X → Set where
  [] : ∀ {xs} → [] ≺ xs
  _∷_ : ∀ x {xs' xs} → xs' ≺ xs → x ∷ xs' ≺ x ∷ xs

≺-refl : ∀ (xs : List X) → xs ≺ xs
≺-refl [] = []
≺-refl (x ∷ xs) = x ∷ ≺-refl xs

≺-trans : ∀ {xs ys zs : List X} → xs ≺ ys → ys ≺ zs → xs ≺ zs
≺-trans [] _ = []
≺-trans (x ∷ pf) (.x ∷ pf') = x ∷ ≺-trans pf pf'

shift-≺-∷ : ∀ (x : X) xs → shift x xs ≺ (x ∷ xs)
shift-≺-∷ x [] = []
shift-≺-∷ x (x' ∷ xs) = x ∷ shift-≺-∷ x' xs

≺-cong-shift : ∀ (x : X) → _≺_ =[ shift x ]⇒ _≺_
≺-cong-shift x [] = []
≺-cong-shift x (x' ∷ pf) = x ∷ ≺-cong-shift x' pf

≺-cong-zip : zip {A = X} {B = Y} Preserves₂ _≺_ ⟶ _≺_ ⟶ _≺_
≺-cong-zip [] _ = []
≺-cong-zip (_ ∷ _) [] = []
≺-cong-zip (x ∷ pf) (y ∷ pf') = (x , y) ∷ ≺-cong-zip pf pf'

≺-unzip₁ : _≺_ =[ proj₁ ∘ unzip {A = X} {B = Y} ]⇒ _≺_
≺-unzip₁ [] = []
≺-unzip₁ (xy ∷ p) = proj₁ xy ∷ ≺-unzip₁ p

≺-unzip₂ : _≺_ =[ proj₂ ∘ unzip {A = X} {B = Y} ]⇒ _≺_
≺-unzip₂ [] = []
≺-unzip₂ (xy ∷ p) = proj₂ xy ∷ ≺-unzip₂ p

unzip-zip₁ : ∀ (xs : List X) (ys : List Y) → proj₁ (unzip (zip xs ys)) ≺ xs
unzip-zip₁ [] _ = []
unzip-zip₁ (x ∷ xs) [] = []
unzip-zip₁ (x ∷ xs) (y ∷ ys) = x ∷ unzip-zip₁ xs ys

unzip-zip₂ : ∀ (xs : List X) (ys : List Y) → proj₂ (unzip (zip xs ys)) ≺ ys
unzip-zip₂ [] _ = []
unzip-zip₂ (x ∷ xs) [] = []
unzip-zip₂ (x ∷ xs) (y ∷ ys) = y ∷ unzip-zip₂ xs ys

-------------------------------------------------------------------------------
-- Sequence transformation

ST : Set → Set → Set
ST X Y = List X ⇀ List Y

IsIncremental : ST X Y → Set
IsIncremental st = ∀ {xs' xs ys}
  → xs' ≺ xs
  → st xs ≡ just ys
  → ∃[ ys' ] (ys' ≺ ys) × (st xs' ≡ just ys')

HasDelay : ℕ → ST X Y → Set
HasDelay d st = ∀ xs {ys}
  → st xs ≡ just ys
  → length ys ≡ length xs ∸ d

-- Is d -IST st : st is a d-incremental sequence transformation
record Is_-IST_ (d : ℕ) (st : ST X Y) : Set where
  field
    empty : st [] ≡ just []
    isIncremental : IsIncremental st
    hasDelay : HasDelay d st

-- st' IsIISTOf st : st' is a inverse sequence transformation of st
_IsIISTOf_ : ST X Y → ST Y X → Set
st' IsIISTOf st = ∀ {xs ys}
  → st xs ≡ just ys
  → ∃[ xs' ] (xs' ≺ xs) × (st' ys ≡ just xs')

-- st' Is d -IISTOf st : st' is a d-inverse sequence transformation of st
record _Is_-IISTOf_ (st' : ST X Y) (d : ℕ) (st : ST Y X) : Set where
  field
    is-d-IST : Is d -IST st'
    isIIST : st' IsIISTOf st

-- Is⟨ d , d' ⟩-IIST st : st is a (d, d')-invertible sequence transformation
record Is⟨_,_⟩-IIST_ (d d' : ℕ) (st : ST X Y) : Set where
  field
    inverse : ST Y X
    is-d-IST : Is d -IST st
    inverse-is-d'-IIST : inverse Is d' -IISTOf st

-------------------------------------------------------------------------------
-- IIST constructors and semantics

-- Parallel composition
_⊗_ : ST X Y → ST Z W → ST (X × Z) (Y × W)
(f ⊗ g) xzs =
  let xs , zs = unzip xzs
   in (| zip (f xs) (g zs) |)

-- Forward semantics
F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST X Y
F-map-fold a f g [] = pure []
F-map-fold a f g (x ∷ xs) = (| f a .to x ∷ F-map-fold (g a x) f g xs |)

F⟦_⟧ : E X Y → ST X Y
F⟦ `map-fold a f g ⟧ = F-map-fold a f g
F⟦ `delay x ⟧ = pure ∘ shift x
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
B⟦ `hasten x ⟧ = pure ∘ shift x
B⟦ e `⋙ e' ⟧ = B⟦ e' ⟧ >=> B⟦ e ⟧
B⟦ e `⊗ e' ⟧ = B⟦ e ⟧ ⊗ B⟦ e' ⟧


_ : F⟦ `delay 0 `⋙ `hasten 0 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ [])
_ = refl

_ : B⟦ `delay 0 `⋙ `hasten 0 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ [])
_ = refl

_ : F⟦ `delay 0 `⋙ `hasten 1 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ nothing
_ = refl

_ : F⟦ `delay 0 `⊗ `hasten 0 ⟧ ((1 , 0) ∷ (2 , 1) ∷ (3 , 2) ∷ (4 , 3) ∷ [])
    ≡ just ((0 , 1) ∷ (1 , 2) ∷ (2 , 3) ∷ [])
_ = refl

-------------------------------------------------------------------------------

F-empty : ∀ (e : E X Y) → F⟦ e ⟧ [] ≡ just []
F-empty (`map-fold a f g) = refl
F-empty (`delay x) = refl
F-empty (`hasten x) = refl
F-empty (e `⋙ e') rewrite F-empty e | F-empty e' = refl
F-empty (e `⊗ e') rewrite F-empty e | F-empty e' = refl

B-empty : ∀ (e : E X Y) → B⟦ e ⟧ [] ≡ just []
B-empty (`map-fold a f g) = refl
B-empty (`delay x) = refl
B-empty (`hasten x) = refl
B-empty (e `⋙ e') rewrite B-empty e' | B-empty e = refl
B-empty (e `⊗ e') rewrite B-empty e | B-empty e' = refl

-------------------------------------------------------------------------------
-- Incrementality of F and B

shift-incremental : ∀ (x : X) → IsIncremental (pure ∘ shift x)
shift-incremental x pfx refl = _ , ≺-cong-shift x pfx , refl

unshift-incremental : ∀ {{_ : Eq X}} (x : X) → IsIncremental (unshift x)
unshift-incremental x [] eq = [] , [] , refl
unshift-incremental x (x' ∷ pfx) eq
  with yes refl ← x ≟ x'
  rewrite sym (just-injective eq) =
    _ , pfx , refl

>=>-incremental : ∀ {f : ST X Y} {g : ST Y Z}
  → IsIncremental f
  → IsIncremental g
  → IsIncremental (f >=> g)
>=>-incremental {f = f} {g} f-inc g-inc {xs'} {xs} xs'≺xs eq
  with just ys ← f xs in eq₁
  with just ys' ← f xs' | _ , ys'≺ys , refl ← f-inc xs'≺xs eq₁
  with just zs' ← g ys' | _ , zs'≺zs , refl ← g-inc ys'≺ys eq =
    zs' , zs'≺zs , refl

⊗-incremental : ∀ {f : ST X Y} {g : ST Z W}
  → IsIncremental f
  → IsIncremental g
  → IsIncremental (f ⊗ g)
⊗-incremental {f = f} {g} f-inc g-inc {xzs'} {xzs} xzs'≺xzs eq
  with just ys ← f (unzip xzs .proj₁) in eq₁
  with just ys' ← f (unzip xzs' .proj₁) | _ , ys'≺ys , refl ← f-inc (≺-unzip₁ xzs'≺xzs) eq₁
  with just ws ← g (unzip xzs .proj₂) in eq₂
  with just ws' ← g (unzip xzs' .proj₂) | _ , ws'≺ws , refl ← g-inc (≺-unzip₂ xzs'≺xzs) eq₂
  rewrite sym (just-injective eq) =
    zip ys' ws' , ≺-cong-zip ys'≺ys ws'≺ws , refl

F-incremental : ∀ (e : E X Y) → IsIncremental F⟦ e ⟧
F-incremental (`map-fold a f g) = helper a
  where
    helper : ∀ a → IsIncremental F⟦ `map-fold a f g ⟧
    helper a [] eq = [] , [] , refl
    helper a (_∷_ x {xs'} {xs} xs'≺xs) eq
      with just y ← f a .to x
      with just ys ← F-map-fold (g a x) f g xs in eq₁
      with just ys' ← F-map-fold (g a x) f g xs' | _ , ys'≺ys , refl ← helper (g a x) xs'≺xs eq₁
      rewrite sym (just-injective eq) =
        y ∷ ys' , y ∷ ys'≺ys , refl
F-incremental (`delay x) = shift-incremental x
F-incremental (`hasten x) = unshift-incremental x
F-incremental (e `⋙ e') = >=>-incremental (F-incremental e) (F-incremental e')
F-incremental (e `⊗ e') = ⊗-incremental (F-incremental e) (F-incremental e')

B-incremental : ∀ (e : E X Y) → IsIncremental B⟦ e ⟧
B-incremental (`map-fold a f g) = helper a
  where
    helper : ∀ a → IsIncremental B⟦ `map-fold a f g ⟧
    helper a [] eq = [] , [] , refl
    helper a (_∷_ y {ys'} {ys} ys'≺ys) eq
      with just x ← f a .from y
      with just xs ← B-map-fold (g a x) f g ys in eq₁
      with just xs' ← B-map-fold (g a x) f g ys' | _ , xs'≺xs , refl ← helper (g a x) ys'≺ys eq₁
      rewrite sym (just-injective eq) =
        x ∷ xs' , x ∷ xs'≺xs , refl
B-incremental (`delay x) = unshift-incremental x
B-incremental (`hasten x) = shift-incremental x
B-incremental (e `⋙ e') = >=>-incremental (B-incremental e') (B-incremental e)
B-incremental (e `⊗ e') = ⊗-incremental (B-incremental e) (B-incremental e')

--------------------------------------------------------------------------------
-- d-incrementality of F and B

shift-hasDelay : ∀ (x : X) → HasDelay 0 (pure ∘ shift x)
shift-hasDelay x [] refl = refl
shift-hasDelay x (y ∷ xs) refl = cong suc (shift-hasDelay y xs refl)

unshift-hasDelay : ∀ {{_ : Eq X}} (x : X) → HasDelay 1 (unshift x)
unshift-hasDelay x [] refl = refl
unshift-hasDelay x (y ∷ xs) eq with yes refl ← x ≟ y =
  sym (cong length (just-injective eq))

>=>-hasDelay : ∀ {d d'} {f : ST X Y} {g : ST Y Z}
  → HasDelay d f
  → HasDelay d' g
  → HasDelay (d + d') (f >=> g)
>=>-hasDelay {d = d} {d'} {f} {g} p q xs eq
  with just ys ← f xs in eq₁
  rewrite q ys eq | p xs eq₁ =
    ∸-+-assoc (length xs) d d'

⊗-hasDelay : ∀ {d d'} {f : ST X Y} {g : ST Z W}
  → HasDelay d f
  → HasDelay d' g
  → HasDelay (d ⊔ d') (f ⊗ g)
⊗-hasDelay {d = d} {d'} {f} {g} f-delay g-delay xzs eq
  with just ys ← f (unzip xzs .proj₁) in eq₁
  with just ws ← g (unzip xzs .proj₂) in eq₂
  rewrite sym (just-injective eq)
        | length-zipWith _,_ ys ws
        | f-delay (unzip xzs .proj₁) eq₁
        | g-delay (unzip xzs .proj₂) eq₂
        | length-unzipWith₁ id xzs
        | length-unzipWith₂ id xzs =
    sym (∸-distribˡ-⊔-⊓ (length xzs) d d')

F-hasDelay : ∀ (e : E X Y) → HasDelay DF⟦ e ⟧ F⟦ e ⟧
F-hasDelay (`map-fold a f g) = helper a
  where
    helper : ∀ a → HasDelay 0 F⟦ `map-fold a f g ⟧
    helper a [] refl = refl
    helper a (x ∷ xs) eq
      with just y ← f a .to x
      with just ys ← F-map-fold (g a x) f g xs in eq₁
      rewrite sym (just-injective eq) =
        cong suc (helper (g a x) xs eq₁)
F-hasDelay (`delay x) = shift-hasDelay x
F-hasDelay (`hasten x) = unshift-hasDelay x
F-hasDelay (e `⋙ e') = >=>-hasDelay {d = DF⟦ e ⟧} {d' = DF⟦ e' ⟧} (F-hasDelay e) (F-hasDelay e')
F-hasDelay (e `⊗ e') = ⊗-hasDelay {d = DF⟦ e ⟧} {d' = DF⟦ e' ⟧} (F-hasDelay e) (F-hasDelay e')

B-hasDelay : ∀ (e : E X Y) → HasDelay DB⟦ e ⟧ B⟦ e ⟧
B-hasDelay (`map-fold a f g) = helper a
  where
    helper : ∀ a → HasDelay 0 B⟦ `map-fold a f g ⟧
    helper a [] refl = refl
    helper a (y ∷ ys) eq
      with just x ← f a .from y
      with just xs ← B-map-fold (g a x) f g ys in eq₁
      rewrite sym (just-injective eq) =
        cong suc (helper (g a x) ys eq₁)
B-hasDelay (`delay x) = unshift-hasDelay x
B-hasDelay (`hasten x) = shift-hasDelay x
B-hasDelay (e `⋙ e') = >=>-hasDelay {d = DB⟦ e' ⟧} {d' = DB⟦ e ⟧} (B-hasDelay e') (B-hasDelay e)
B-hasDelay (e `⊗ e') = ⊗-hasDelay {d = DB⟦ e ⟧} {d' = DB⟦ e' ⟧} (B-hasDelay e) (B-hasDelay e')

--------------------------------------------------------------------------------
-- F and B are inverse of each other

shift-IIST : ∀ {{_ : Eq X}} (x : X) → (pure ∘ shift x) IsIISTOf unshift x
shift-IIST x {[]} refl = [] , [] , refl
shift-IIST x {y ∷ xs} eq
  with yes refl ← x ≟ y
  rewrite sym (just-injective eq) =
    shift y xs , shift-≺-∷ x xs , refl

unshift-IIST : ∀ {{_ : Eq X}} (x : X) → unshift x IsIISTOf (pure ∘ shift x)
unshift-IIST x {[]} refl = [] , [] , refl
unshift-IIST x {y ∷ xs} refl with x ≟ x
... | no contra with () ← contra refl
... | yes refl = shift y xs , shift-≺-∷ y xs , refl

>=>-IIST : ∀ {f : ST X Y} {f' : ST Y X} {g : ST Y Z} {g' : ST Z Y}
  → f IsIISTOf f'
  → g IsIISTOf g'
  → IsIncremental g
  → (f >=> g) IsIISTOf (g' >=> f')
>=>-IIST {f = f} {f'} {g} {g'} f-inv-f' g-inv-g' g-inc {zs} {xs} eq
  with just ys ← g' zs in eq₁
  with just zs' ← g ys in eq₂ | _ , zs'≺zs , refl ← g-inv-g' eq₁
  with just ys' ← f xs | _ , ys'≺ys , refl ← f-inv-f' eq
  with zs'' , zs''≺zs' , eq₃ ← g-inc ys'≺ys eq₂ =
    zs'' , ≺-trans zs''≺zs' zs'≺zs , eq₃

⊗-IIST : ∀ {f : ST X Y} {f' : ST Y X} {g : ST Z W} {g' : ST W Z}
  → f IsIISTOf f'
  → g IsIISTOf g'
  → IsIncremental f
  → IsIncremental g
  → (f ⊗ g) IsIISTOf (f' ⊗ g')
⊗-IIST {f = f} {f'} {g} {g'} f-inv-f' g-inv-g' f-inc g-inc {yws} eq
  with just xs ← f' (unzip yws .proj₁) in eq₁
  with just ys' ← f xs in eq₁ | _ , ys'≺ys , refl ← f-inv-f' eq₁
  with just zs ← g' (unzip yws .proj₂) in eq₂
  with just ws' ← g zs in eq₂ | _ , ws'≺ws , refl ← g-inv-g' eq₂
  rewrite sym (just-injective eq)
  with just ys'' ← f (unzip (zip xs zs) .proj₁) | _ , ys''≺ys' , refl ← f-inc (unzip-zip₁ xs zs) eq₁
  with just ws'' ← g (unzip (zip xs zs) .proj₂) | _ , ws''≺ws' , refl ← g-inc (unzip-zip₂ xs zs) eq₂ =
    zip ys'' ws'' ,
    ≺-trans (≺-cong-zip ys''≺ys' ws''≺ws') (subst (zip ys' ws' ≺_) (zip-unzip yws) (≺-cong-zip ys'≺ys ws'≺ws)) ,
    refl

F-IIST : ∀ (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (`map-fold a f g) = helper a
  where
    helper : ∀ a → F⟦ `map-fold a f g ⟧ IsIISTOf B⟦ `map-fold a f g ⟧
    helper a {[]} refl = [] , [] , refl
    helper a {y ∷ ys} eq
      with just x ← f a .from y in eq₁
      with just xs ← B-map-fold (g a x) f g ys in eq₂
      rewrite sym (just-injective eq) | f a .from→to eq₁
      with just ys' ← F-map-fold (g a x) f g xs | _ , ys'≺ys , refl ← helper (g a x) {ys} eq₂ =
        y ∷ ys' , y ∷ ys'≺ys , refl
F-IIST (`delay x) = shift-IIST x
F-IIST (`hasten x) = unshift-IIST x
F-IIST (e `⋙ e') = >=>-IIST (F-IIST e) (F-IIST e') (F-incremental e')
F-IIST (e `⊗ e') = ⊗-IIST (F-IIST e) (F-IIST e') (F-incremental e) (F-incremental e')

B-IIST : ∀ (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (`map-fold a f g) = helper a
  where
    helper : ∀ a → B⟦ `map-fold a f g ⟧ IsIISTOf F⟦ `map-fold a f g ⟧
    helper a {[]} refl = [] , [] , refl
    helper a {x ∷ xs} eq
      with just y ← f a .to x in eq₁
      with just ys ← F-map-fold (g a x) f g xs in eq₂
      rewrite sym (just-injective eq) | f a .to→from eq₁
      with just xs' ← B-map-fold (g a x) f g ys | _ , xs'≺xs , refl ← helper (g a x) {xs} eq₂ =
        x ∷ xs' , x ∷ xs'≺xs , refl
B-IIST (`delay x) = unshift-IIST x
B-IIST (`hasten x) = shift-IIST x
B-IIST (e `⋙ e') = >=>-IIST (B-IIST e') (B-IIST e) (B-incremental e)
B-IIST (e `⊗ e') = ⊗-IIST (B-IIST e) (B-IIST e') (B-incremental e) (B-incremental e')

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

F∘I≡B : ∀ (e : E X Y) (ys : List Y) → F⟦ I⟦ e ⟧ ⟧ ys ≡ B⟦ e ⟧ ys
F∘I≡B (`map-fold a f g) = helper a
  where
    helper : ∀ a ys → F⟦ I⟦ `map-fold a f g ⟧ ⟧ ys ≡ B⟦ `map-fold a f g ⟧ ys
    helper a [] = refl
    helper a (y ∷ ys) with f a .from y in eq
    ... | nothing = refl
    ... | just x rewrite helper (g a x) ys = refl
F∘I≡B (`delay x) xs = refl
F∘I≡B (`hasten x) xs = refl
F∘I≡B (e `⋙ e') zs rewrite F∘I≡B e' zs with B⟦ e' ⟧ zs
... | nothing = refl
... | just ys = F∘I≡B e ys
F∘I≡B (e `⊗ e') xzs rewrite F∘I≡B e (unzip xzs .proj₁) | F∘I≡B e' (unzip xzs .proj₂) =
  refl

B∘I≡F : ∀ (e : E X Y) (xs : List X) → B⟦ I⟦ e ⟧ ⟧ xs ≡ F⟦ e ⟧ xs
B∘I≡F (`map-fold a f g) = helper a
  where
    helper : ∀ a xs → B⟦ I⟦ `map-fold a f g ⟧ ⟧ xs ≡ F⟦ `map-fold a f g ⟧ xs
    helper a [] = refl
    helper a (x ∷ xs) with f a .to x in eq
    ... | nothing = refl
    ... | just y rewrite f a .to→from eq | helper (g a x) xs = refl
B∘I≡F (`delay x) xs = refl
B∘I≡F (`hasten x) xs = refl
B∘I≡F (e `⋙ e') xs rewrite B∘I≡F e xs with F⟦ e ⟧ xs
... | nothing = refl
... | just ys = B∘I≡F e' ys
B∘I≡F (e `⊗ e') xzs rewrite B∘I≡F e (unzip xzs .proj₁) | B∘I≡F e' (unzip xzs .proj₂) =
  refl
