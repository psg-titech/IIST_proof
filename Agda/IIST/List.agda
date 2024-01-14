module IIST.List where

open import Level using ( 0ℓ )
open import Data.List.Base using ( List; []; _∷_; zip; unzip; length )
open import Data.List.Properties using ( length-zipWith; length-unzipWith₁; length-unzipWith₂; zipWith-unzipWith; length-++ )
open import Data.Maybe.Base using ( Maybe; just; nothing; maybe; _>>=_ )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Maybe.Effectful using () renaming ( monad to monadMaybe )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _∸_; _⊔_ )
open import Data.Nat.Instances
open import Data.Nat.Properties using ( +-comm; ∸-+-assoc; ∸-distribˡ-⊔-⊓; suc-injective )
open import Data.Product.Base using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Effect.Monad using ( RawMonad )
open import Function using ( id; _∘_; case_of_ )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong; sym; trans )

open import IIST.Common
open import IIST.Syntax

open RawMonad {0ℓ} monadMaybe using ( return; _>=>_ )

private
  variable
    A X Y Z W : Set

-------------------------------------------------------------------------------
-- Additional functions and relations on lists

infix 4 _≺_

shift : X → List X → List X
shift _ [] = []
shift x (y ∷ xs) = x ∷ shift y xs

_ : shift 0 (1 ∷ 2 ∷ 3 ∷ []) ≡ 0 ∷ 1 ∷ 2 ∷ []
_ = refl

unshift : {{_ : Eq X}} → X → List X ⇀ List X
unshift x [] = just []
unshift x (y ∷ xs) = case x ≟ y of λ
  { (no _) → nothing
  ; (yes _) → just xs
  }

length-unzip : ∀ {xzs : List (X × Z)} {xs zs}
  → unzip xzs ≡ (xs , zs)
  → length xzs ≡ length xs × length xzs ≡ length zs
length-unzip {xzs = []} refl = refl , refl
length-unzip {xzs = (x , z) ∷ xzs} refl
  with xs , zs ← unzip xzs in eq
  with ih₁ , ih₂ ← length-unzip eq =
    cong suc ih₁ , cong suc ih₂

unzip-zip : ∀ {xzs : List (X × Z)} {xs zs}
  → unzip xzs ≡ (xs , zs)
  → zip xs zs ≡ xzs
unzip-zip {xzs = xzs} refl = zipWith-unzipWith id _,_ (λ _ → refl) xzs


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

≺-cong-shift : ∀ (x : X) {xs' xs} → xs' ≺ xs → shift x xs' ≺ shift x xs
≺-cong-shift x [] = []
≺-cong-shift x (x' ∷ pf) = x ∷ ≺-cong-shift x' pf

≺-cong-zip : ∀ {xs' xs : List X} {ys' ys : List Y}
  → xs' ≺ xs
  → ys' ≺ ys
  → zip xs' ys' ≺ zip xs ys
≺-cong-zip [] _ = []
≺-cong-zip (_ ∷ _) [] = []
≺-cong-zip (x ∷ pf) (y ∷ pf') = (x , y) ∷ ≺-cong-zip pf pf'

≺-unzip : ∀ {xys' xys : List (X × Y)} {xs' ys' xs ys}
  → xys' ≺ xys
  → unzip xys' ≡ (xs' , ys')
  → unzip xys ≡ (xs , ys)
  → (xs' ≺ xs) × (ys' ≺ ys)
≺-unzip [] refl refl = [] , []
≺-unzip (_∷_ (x , y) {xs' = xys'} {xs = xys} pfxy) refl refl
  with xs' , ys' ← unzip xys' in eq'
  with xs , ys ← unzip xys in eq
  with pfx , pfy ← ≺-unzip pfxy eq' eq =
    x ∷ pfx , y ∷ pfy

zip-unzip : ∀ {xs : List X} {ys : List Y} {xs' ys'}
  → unzip (zip xs ys) ≡ (xs' , ys')
  → (xs' ≺ xs) × (ys' ≺ ys)
zip-unzip {xs = []} refl = [] , []
zip-unzip {xs = x ∷ xs} {[]} refl = [] , []
zip-unzip {xs = x ∷ xs} {y ∷ ys} refl
  with xs' , ys' ← unzip (zip xs ys) in eq
  with pfx , pfy ← zip-unzip eq =
    x ∷ pfx , y ∷ pfy

-------------------------------------------------------------------------------
-- Sequence transformation

ST : Set → Set → Set
ST X Y = List X ⇀ List Y

IsIncremental : ST X Y → Set
IsIncremental st = ∀ {xs ys}
  → st xs ≡ just ys
  → ∀ {xs'} → xs' ≺ xs
  → Σ[ ys' ∈ _ ] (ys' ≺ ys) × (st xs' ≡ just ys')

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
  → Σ[ xs' ∈ _ ] (xs' ≺ xs) × (st' ys ≡ just xs')

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
_∥_ : ST X Y → ST Z W → ST (X × Z) (Y × W)
(f ∥ g) xzs = do
  let xs , zs = unzip xzs
  ys ← f xs
  ws ← g zs
  return (zip ys ws)

-- Forward semantics
F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST X Y
F-map-fold a f g [] = return []
F-map-fold a f g (x ∷ xs) = do
  y ← f a .to x
  ys ← F-map-fold (g a x) f g xs
  return (y ∷ ys)

F⟦_⟧ : E X Y → ST X Y
F⟦ map-fold a f g ⟧ = F-map-fold a f g
F⟦ delay x ⟧ = return ∘ shift x
F⟦ hasten x ⟧ = unshift x
F⟦ e ⋙ e' ⟧ = F⟦ e ⟧ >=> F⟦ e' ⟧
F⟦ e ⊗ e' ⟧ = F⟦ e ⟧ ∥ F⟦ e' ⟧


-- Backward semantics
B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST Y X
B-map-fold a f g [] = just []
B-map-fold a f g (y ∷ ys) = do
  x ← f a .from y
  xs ← B-map-fold (g a x) f g ys
  just (x ∷ xs)

B⟦_⟧ : E X Y → ST Y X
B⟦ map-fold a f g ⟧ = B-map-fold a f g
B⟦ delay x ⟧ = unshift x
B⟦ hasten x ⟧ = return ∘ shift x
B⟦ e ⋙ e' ⟧ = B⟦ e' ⟧ >=> B⟦ e ⟧
B⟦ e ⊗ e' ⟧ = B⟦ e ⟧ ∥ B⟦ e' ⟧


_ : F⟦ delay 0 ⋙ hasten 0 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ [])
_ = refl

_ : B⟦ delay 0 ⋙ hasten 0 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ [])
_ = refl

_ : F⟦ delay 0 ⋙ hasten 1 ⟧ (1 ∷ 2 ∷ 3 ∷ []) ≡ nothing
_ = refl

_ : F⟦ delay 0 ⊗ hasten 0 ⟧ ((1 , 0) ∷ (2 , 1) ∷ (3 , 2) ∷ (4 , 3) ∷ [])
    ≡ just ((0 , 1) ∷ (1 , 2) ∷ (2 , 3) ∷ [])
_ = refl

-------------------------------------------------------------------------------

F-empty : ∀ (e : E X Y) → F⟦ e ⟧ [] ≡ just []
F-empty (map-fold a f g) = refl
F-empty (delay x) = refl
F-empty (hasten x) = refl
F-empty (e ⋙ e') rewrite F-empty e | F-empty e' = refl
F-empty (e ⊗ e') rewrite F-empty e | F-empty e' = refl

B-empty : ∀ (e : E X Y) → B⟦ e ⟧ [] ≡ just []
B-empty (map-fold a f g) = refl
B-empty (delay x) = refl
B-empty (hasten x) = refl
B-empty (e ⋙ e') rewrite B-empty e' | B-empty e = refl
B-empty (e ⊗ e') rewrite B-empty e | B-empty e' = refl

-------------------------------------------------------------------------------
-- Incrementality of F and B

shift-incremental : ∀ (x : X) → IsIncremental (return ∘ shift x)
shift-incremental x refl {xs'} p = shift x xs' , ≺-cong-shift x p , refl

unshift-incremental : ∀ {{_ : Eq X}} (x : X) → IsIncremental (unshift x)
unshift-incremental x eq [] = [] , [] , refl
unshift-incremental x eq (y ∷ p)
  with yes refl ← x ≟ y
  rewrite just-injective eq =
    _ , p , refl

>=>-incremental : ∀ {f : ST X Y} {g : ST Y Z}
  → IsIncremental f
  → IsIncremental g
  → IsIncremental (f >=> g)
>=>-incremental {f = f} {g} p q {xs} eq {xs'} pfx
  with just ys ← f xs in eq₁
  with ys' , pfy , eq₂ ← p eq₁ pfx
  with just zs ← g ys in eq₃
  with zs' , pfz , eq₄ ← q eq₃ pfy
  rewrite sym (just-injective eq) | eq₂ | eq₄ =
    zs' , pfz , refl

∥-incremental : ∀ {f : ST X Y} {g : ST Z W}
  → IsIncremental f
  → IsIncremental g
  → IsIncremental (f ∥ g)
∥-incremental {f = f} {g} p q {xzs} eq {xzs'} pfxz
  with xs' , zs' ← unzip xzs' in eq₁
  with xs , zs ← unzip xzs in eq₂
  with pfx , pfz ← ≺-unzip pfxz eq₁ eq₂
  with just ys ← f xs in eq₃
  with just ws ← g zs in eq₄
  with ys' , pfy , eq₅ ← p eq₃ pfx
  with ws' , pfw , eq₆ ← q eq₄ pfz
  rewrite sym (just-injective eq) | eq₅ | eq₆ =
    zip ys' ws' , ≺-cong-zip pfy pfw , refl

F-incremental : ∀ (e : E X Y) → IsIncremental F⟦ e ⟧
F-incremental (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → IsIncremental F⟦ map-fold a f g ⟧
    helper a eq [] = [] , [] , refl
    helper a eq (_∷_ x {xs = xs} pf)
      with just y ← f a .to x
      with just ys ← F-map-fold (g a x) f g xs in eq₁
      with ys' , pf' , eq₂ ← helper (g a x) eq₁ pf
      rewrite sym (just-injective eq) | eq₂ =
        y ∷ ys' , y ∷ pf' , refl
F-incremental (delay x) = shift-incremental x
F-incremental (hasten x) = unshift-incremental x
F-incremental (e ⋙ e') = >=>-incremental (F-incremental e) (F-incremental e')
F-incremental (e ⊗ e') = ∥-incremental (F-incremental e) (F-incremental e')

B-incremental : ∀ (e : E X Y) → IsIncremental B⟦ e ⟧
B-incremental (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → IsIncremental B⟦ map-fold a f g ⟧
    helper a eq [] = [] , [] , refl
    helper a eq (_∷_ y {xs = ys} pf)
      with just x ← f a .from y
      with just xs ← B-map-fold (g a x) f g ys in eq₁
      with xs' , pf' , eq₂ ← helper (g a x) eq₁ pf
      rewrite sym (just-injective eq) | eq₂ =
        x ∷ xs' , x ∷ pf' , refl
B-incremental (delay x) = unshift-incremental x
B-incremental (hasten x) = shift-incremental x
B-incremental (e ⋙ e') = >=>-incremental (B-incremental e') (B-incremental e)
B-incremental (e ⊗ e') = ∥-incremental (B-incremental e) (B-incremental e')

--------------------------------------------------------------------------------
-- d-incrementality of F and B

shift-hasDelay : ∀ (x : X) → HasDelay 0 (return ∘ shift x)
shift-hasDelay x [] refl = refl
shift-hasDelay x (y ∷ xs) refl = cong suc (shift-hasDelay y xs refl)

unshift-hasDelay : ∀ {{_ : Eq X}} (x : X) → HasDelay 1 (unshift x)
unshift-hasDelay x [] refl = refl
unshift-hasDelay x (y ∷ xs) eq
  with yes refl ← x ≟ y
  rewrite sym (just-injective eq) =
    refl

>=>-hasDelay : ∀ {d d'} {f : ST X Y} {g : ST Y Z}
  → HasDelay d f
  → HasDelay d' g
  → HasDelay (d + d') (f >=> g)
>=>-hasDelay {d = d} {d'} {f} {g} p q xs eq
  with just ys ← f xs in eq₁
  with ih₁ ← p xs eq₁
  with just zs ← g ys in eq₂
  with ih₂ ← q ys eq₂
  rewrite sym (just-injective eq) | ih₁ | ih₂ =
    ∸-+-assoc (length xs) d d'

∥-hasDelay : ∀ {d d'} {f : ST X Y} {g : ST Z W}
  → HasDelay d f
  → HasDelay d' g
  → HasDelay (d ⊔ d') (f ∥ g)
∥-hasDelay {d = d} {d'} {f} {g} p q xzs eq
  with xs , zs ← unzip xzs in eq₁
  with just ys ← f xs in eq₂
  with just ws ← g zs in eq₃
  with ih₁ ← p xs eq₂
  with ih₂ ← q zs eq₃
  rewrite sym (just-injective eq) | length-zipWith _,_ ys ws | ih₁ | ih₂
  with eq₄ , eq₅ ← length-unzip eq₁
  rewrite sym eq₄ | sym eq₅ =
    sym (∸-distribˡ-⊔-⊓ (length xzs) d d')

F-hasDelay : ∀ (e : E X Y) → HasDelay DF⟦ e ⟧ F⟦ e ⟧
F-hasDelay (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → HasDelay 0 F⟦ map-fold a f g ⟧
    helper a [] refl = refl
    helper a (x ∷ xs) eq
      with just y ← f a .to x
      with just ys ← F-map-fold (g a x) f g xs in eq₁
      with ih ← helper (g a x) xs eq₁
      rewrite sym (just-injective eq) =
        cong suc ih
F-hasDelay (delay x) = shift-hasDelay x
F-hasDelay (hasten x) = unshift-hasDelay x
F-hasDelay (e ⋙ e') = >=>-hasDelay {d = DF⟦ e ⟧} {d' = DF⟦ e' ⟧} (F-hasDelay e) (F-hasDelay e')
F-hasDelay (e ⊗ e') = ∥-hasDelay {d = DF⟦ e ⟧} {d' = DF⟦ e' ⟧} (F-hasDelay e) (F-hasDelay e')

B-hasDelay : ∀ (e : E X Y) → HasDelay DB⟦ e ⟧ B⟦ e ⟧
B-hasDelay (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → HasDelay 0 B⟦ map-fold a f g ⟧
    helper a [] refl = refl
    helper a (y ∷ ys) eq
      with just x ← f a .from y
      with just xs ← B-map-fold (g a x) f g ys in eq₁
      with ih ← helper (g a x) ys eq₁
      rewrite sym (just-injective eq) =
        cong suc ih
B-hasDelay (delay x) = unshift-hasDelay x
B-hasDelay (hasten x) = shift-hasDelay x
B-hasDelay (e ⋙ e') = >=>-hasDelay {d = DB⟦ e' ⟧} {d' = DB⟦ e ⟧} (B-hasDelay e') (B-hasDelay e)
B-hasDelay (e ⊗ e') = ∥-hasDelay {d = DB⟦ e ⟧} {d' = DB⟦ e' ⟧} (B-hasDelay e) (B-hasDelay e')

--------------------------------------------------------------------------------
-- F and B are inverse of each other

shift-IIST : ∀ {{_ : Eq X}} (x : X) → (return ∘ shift x) IsIISTOf (unshift x)
shift-IIST x {[]} refl = [] , [] , refl
shift-IIST x {y ∷ xs} eq
  with yes refl ← x ≟ y
  rewrite sym (just-injective eq) =
    shift y xs , shift-≺-∷ x xs , refl

unshift-IIST : ∀ {{_ : Eq X}} (x : X) → (unshift x) IsIISTOf (return ∘ shift x)
unshift-IIST x {[]} refl = [] , [] , refl
unshift-IIST x {y ∷ xs} refl with x ≟ x
... | no contra with () ← contra refl
... | yes refl = shift y xs , shift-≺-∷ y xs , refl

>=>-IIST : ∀ {f : ST X Y} {f' : ST Y X} {g : ST Y Z} {g' : ST Z Y}
  → f IsIISTOf f'
  → g IsIISTOf g'
  → IsIncremental g
  → (f >=> g) IsIISTOf (g' >=> f')
>=>-IIST {f = f} {f'} {g} {g'} p q r {zs} {xs} eq
  with just ys ← g' zs in eq₁
  with zs' , pfz , eq₁ ← q eq₁
  with just xs ← f' ys in eq₂
  with ys' , pfy , eq₂ ← p eq₂
  with zs'' , pfz' , eq₃ ← r eq₁ pfy
  rewrite sym (just-injective eq) | eq₁ | eq₂ =
    zs'' , ≺-trans pfz' pfz , eq₃

∥-IIST : ∀ {f : ST X Y} {f' : ST Y X} {g : ST Z W} {g' : ST W Z}
  → f IsIISTOf f'
  → g IsIISTOf g'
  → IsIncremental f
  → IsIncremental g
  → (f ∥ g) IsIISTOf (f' ∥ g')
∥-IIST {f = f} {f'} {g} {g'} p q r s {yws} eq
  with ys , ws ← unzip yws in eq₁
  with just xs ← f' ys in eq₂
  with just zs ← g' ws in eq₃
  with ys' , pfy , eq₂ ← p eq₂
  with ws' , pfw , eq₃ ← q eq₃
  rewrite sym (just-injective eq)
  with xs' , zs' ← unzip (zip xs zs) in eq₄
  with pfx , pfz ← zip-unzip eq₄
  with ys'' , pfy' , eq₅ ← r eq₂ pfx
  with ws'' , pfw' , eq₆ ← s eq₃ pfz
  rewrite sym (unzip-zip eq₁) | eq₅ | eq₆ =
    zip ys'' ws'' , ≺-cong-zip (≺-trans pfy' pfy) (≺-trans pfw' pfw) , refl

F-IIST : ∀ (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (map-fold {A = A} a f g) = helper a
  where
    helper : (a : A) → F⟦ map-fold a f g ⟧ IsIISTOf B⟦ map-fold a f g ⟧
    helper a {[]} refl = [] , [] , refl
    helper a {y ∷ ys} eq
      with just x ← f a .from y in eq₁
      with just xs ← B-map-fold (g a x) f g ys in eq₂
      rewrite sym (just-injective eq) | f a .from→to eq₁
      with ys' , pf , eq₃ ← helper (g a x) {ys} eq₂
      rewrite eq₃ =
        y ∷ ys' , y ∷ pf , refl
F-IIST (delay x) = shift-IIST x
F-IIST (hasten x) = unshift-IIST x
F-IIST (e ⋙ e') = >=>-IIST (F-IIST e) (F-IIST e') (F-incremental e')
F-IIST (e ⊗ e') = ∥-IIST (F-IIST e) (F-IIST e') (F-incremental e) (F-incremental e')

B-IIST : ∀ (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (map-fold {A = A} a f g) = helper a
  where
    helper : (a : A) → B⟦ map-fold a f g ⟧ IsIISTOf F⟦ map-fold a f g ⟧
    helper a {[]} refl = [] , [] , refl
    helper a {x ∷ xs} eq
      with just y ← f a .to x in eq₁
      with just ys ← F-map-fold (g a x) f g xs in eq₂
      rewrite sym (just-injective eq) | f a .to→from eq₁
      with xs' , pf , eq₃ ← helper (g a x) {xs} eq₂
      rewrite eq₃ =
        x ∷ xs' , x ∷ pf , refl
B-IIST (delay x) = unshift-IIST x
B-IIST (hasten x) = shift-IIST x
B-IIST (e ⋙ e') = >=>-IIST (B-IIST e') (B-IIST e) (B-incremental e)
B-IIST (e ⊗ e') = ∥-IIST (B-IIST e) (B-IIST e') (B-incremental e) (B-incremental e')

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
F∘I≡B {Y = Y} (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) (ys : List Y)
      → F⟦ I⟦ map-fold a f g ⟧ ⟧ ys ≡ B⟦ map-fold a f g ⟧ ys
    helper a [] = refl
    helper a (y ∷ ys) with f a .from y in eq
    ... | nothing = refl
    ... | just x rewrite f a .from→to eq | helper (g a x) ys = refl
F∘I≡B (delay x) xs = refl
F∘I≡B (hasten x) xs = refl
F∘I≡B (e ⋙ e') zs rewrite F∘I≡B e' zs with B⟦ e' ⟧ zs
... | nothing = refl
... | just ys = F∘I≡B e ys
F∘I≡B (e ⊗ e') xzs
  with xs , zs ← unzip xzs
  rewrite F∘I≡B e xs | F∘I≡B e' zs =
    refl

B∘I≡F : ∀ (e : E X Y) (xs : List X) → B⟦ I⟦ e ⟧ ⟧ xs ≡ F⟦ e ⟧ xs
B∘I≡F {X} (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) (xs : List X)
      → B⟦ I⟦ map-fold a f g ⟧ ⟧ xs ≡ F⟦ map-fold a f g ⟧ xs
    helper a [] = refl
    helper a (x ∷ xs) with f a .to x in eq
    ... | nothing = refl
    ... | just y rewrite f a .to→from eq | helper (g a x) xs = refl
B∘I≡F (delay x) xs = refl
B∘I≡F (hasten x) xs = refl
B∘I≡F (e ⋙ e') xs rewrite B∘I≡F e xs with F⟦ e ⟧ xs
... | nothing = refl
... | just ys = B∘I≡F e' ys
B∘I≡F (e ⊗ e') xzs
  with xs , zs ← unzip xzs
  rewrite B∘I≡F e xs | B∘I≡F e' zs =
    refl
