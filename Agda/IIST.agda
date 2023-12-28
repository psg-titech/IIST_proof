module IIST where

open import Data.List.Base using ( List; []; _∷_; zip; unzip; length; _∷ʳ_; initLast;  _∷ʳ′_ )
open import Data.List.Properties using ( length-zipWith; zipWith-unzipWith; length-++ )
open import Data.Maybe.Base using ( Maybe; just; nothing; maybe; _>>=_ )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _∸_; _⊔_ )
open import Data.Nat.Instances
open import Data.Nat.Properties using ( +-comm; ∸-+-assoc; ∸-distribˡ-⊔-⊓; suc-injective )
open import Data.Product.Base using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Function using ( id; _∘_ )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong; sym )

open import IIST.Common
open import IIST.Syntax

private
  variable
    A X Y Z W : Set

-------------------------------------------------------------------------------
-- Additional functions and relations on lists

shift : X → List X → List X
shift _ [] = []
shift x (y ∷ xs) = x ∷ shift y xs

_ : shift 0 (1 ∷ 2 ∷ 3 ∷ []) ≡ 0 ∷ 1 ∷ 2 ∷ []
_ = refl

length-shift : ∀ (x : X) xs → length (shift x xs) ≡ length xs
length-shift x [] = refl
length-shift x (y ∷ xs) = cong suc (length-shift y xs)

length-snoc : ∀ (x : X) xs → length (xs ∷ʳ x) ≡ suc (length xs)
length-snoc x xs rewrite length-++ xs {x ∷ []} = +-comm (length xs) 1

List-induction-reverse : ∀ {P : List X → Set}
  → P []
  → (∀ x {xs} → P xs → P (xs ∷ʳ x))
  → ∀ xs → P xs
List-induction-reverse {X} {P} base step xs = ind (length xs) xs refl
  where
    ind : ∀ n → (xs : List X) → length xs ≡ n → P xs
    ind n xs eq with initLast xs
    ind zero .[] _ | [] = base
    ind zero .(xs ∷ʳ x) eq | xs ∷ʳ′ x rewrite length-snoc x xs with eq
    ... | ()
    ind (suc n) .(xs ∷ʳ x) eq | xs ∷ʳ′ x rewrite length-snoc x xs =
      step x (ind n xs (suc-injective eq))

length-unzip : ∀ {xzs : List (X × Z)} {xs zs}
  → unzip xzs ≡ (xs , zs)
  → length xzs ≡ length xs × length xzs ≡ length zs
length-unzip {xzs = []} refl = refl , refl
length-unzip {xzs = (x , z) ∷ xzs} refl
  with xs , zs ← unzip xzs in eq
  with ih₁ , ih₂ ← length-unzip eq =
    cong suc ih₁ , cong suc ih₂

zip-unzip : ∀ {xzs : List (X × Z)} {xs zs}
  → unzip xzs ≡ (xs , zs)
  → zip xs zs ≡ xzs
zip-unzip {xzs = xzs} refl = zipWith-unzipWith id _,_ (λ _ → refl) xzs


-- xs' ≺ xs : xs' is a prefix of xs
data _≺_ {X : Set} : List X → List X → Set where
  [] : ∀ {xs} → [] ≺ xs
  _∷_ : ∀ x {xs' xs} → xs' ≺ xs → (x ∷ xs') ≺ (x ∷ xs)

≺-reflexive : ∀ (xs : List X) → xs ≺ xs
≺-reflexive [] = []
≺-reflexive (x ∷ xs) = x ∷ ≺-reflexive xs

≺-trans : ∀ {xs ys zs : List X} → xs ≺ ys → ys ≺ zs → xs ≺ zs
≺-trans [] _ = []
≺-trans (x ∷ pf) (.x ∷ pf') = x ∷ ≺-trans pf pf'

shift-≺-∷ : ∀ (x : X) xs → shift x xs ≺ (x ∷ xs)
shift-≺-∷ x [] = []
shift-≺-∷ x (x' ∷ xs) = x ∷ shift-≺-∷ x' xs

≺-shift : ∀ (x : X) {xs' xs} → xs' ≺ xs → shift x xs' ≺ shift x xs
≺-shift x [] = []
≺-shift x (x' ∷ pf) = x ∷ ≺-shift x' pf

≺-zip : ∀ {xs' xs : List X} {ys' ys : List Y}
  → xs' ≺ xs
  → ys' ≺ ys
  → zip xs' ys' ≺ zip xs ys
≺-zip [] _ = []
≺-zip (_ ∷ _) [] = []
≺-zip (x ∷ pf) (y ∷ pf') = (x , y) ∷ ≺-zip pf pf'

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

≺-zip-unzip : ∀ {xs : List X} {ys : List Y} {xs' ys'}
  → unzip (zip xs ys) ≡ (xs' , ys')
  → (xs' ≺ xs) × (ys' ≺ ys)
≺-zip-unzip {xs = []} refl = [] , []
≺-zip-unzip {xs = x ∷ xs} {[]} refl = [] , []
≺-zip-unzip {xs = x ∷ xs} {y ∷ ys} refl
  with xs' , ys' ← unzip (zip xs ys) in eq
  with pfx , pfy ← ≺-zip-unzip eq =
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
HasDelay d st = ∀ {xs ys}
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

-- Forward semantics
F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST X Y
F-map-fold a f g [] = just []
F-map-fold a f g (x ∷ xs) = do
  y ← f a .to x
  ys ← F-map-fold (g a x) f g xs
  just (y ∷ ys)

F⟦_⟧ : E X Y → ST X Y
F⟦ map-fold a f g ⟧ xs = F-map-fold a f g xs
F⟦ delay x ⟧ xs = just (shift x xs)
F⟦ hasten x ⟧ [] = just []
F⟦ hasten x ⟧ (x' ∷ xs) with x ≟ x'
... | no _ = nothing
... | yes refl = just xs
F⟦ e ⟫ e' ⟧ xs = F⟦ e ⟧ xs >>= F⟦ e' ⟧
F⟦ e ⊗ e' ⟧ xzs = do
  let xs , zs = unzip xzs
  ys ← F⟦ e ⟧ xs
  ws ← F⟦ e' ⟧ zs
  just (zip ys ws)


-- Backward semantics
B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → ST Y X
B-map-fold a f g [] = just []
B-map-fold a f g (y ∷ ys) = do
  x ← f a .from y
  xs ← B-map-fold (g a x) f g ys
  just (x ∷ xs)

B⟦_⟧ : E X Y → ST Y X
B⟦ map-fold a f g ⟧ xs = B-map-fold a f g xs
B⟦ delay x ⟧ [] = just []
B⟦ delay x ⟧ (x' ∷ xs) with x ≟ x'
... | no _ = nothing
... | yes refl = just xs
B⟦ hasten x ⟧ xs = just (shift x xs)
B⟦ e ⟫ e' ⟧ zs = B⟦ e' ⟧ zs >>= B⟦ e ⟧
B⟦ e ⊗ e' ⟧ yws = do
  let ys , ws = unzip yws
  xs ← B⟦ e ⟧ ys
  zs ← B⟦ e' ⟧ ws
  just (zip xs zs)


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
-- Properties of The Forward and Backward Semantics

F-empty : ∀ (e : E X Y) → F⟦ e ⟧ [] ≡ just []
F-empty (map-fold a f g) = refl
F-empty (delay x) = refl
F-empty (hasten x) = refl
F-empty (e ⟫ e') rewrite F-empty e | F-empty e' = refl
F-empty (e ⊗ e') rewrite F-empty e | F-empty e' = refl

B-empty : ∀ (e : E X Y) → B⟦ e ⟧ [] ≡ just []
B-empty (map-fold a f g) = refl
B-empty (delay x) = refl
B-empty (hasten x) = refl
B-empty (e ⟫ e') rewrite B-empty e' | B-empty e = refl
B-empty (e ⊗ e') rewrite B-empty e | B-empty e' = refl


F-incremental : ∀ (e : E X Y) → IsIncremental F⟦ e ⟧
F-incremental (map-fold {A} a f g) = F-map-fold-incremental a
  where
    F-map-fold-incremental : (a : A) → IsIncremental F⟦ map-fold a f g ⟧
    F-map-fold-incremental a eq [] = [] , [] , refl
    F-map-fold-incremental a eq (_∷_ x {xs = xs} pf)
      with just y ← f a .to x
      with just ys ← F-map-fold (g a x) f g xs in eq₁
      with ys' , pf' , eq₂ ← F-map-fold-incremental (g a x) eq₁ pf
      rewrite sym (just-injective eq) | eq₂ =
        y ∷ ys' , y ∷ pf' , refl
F-incremental (delay x) refl {xs'} pf = shift x xs' , ≺-shift x pf , refl
F-incremental (hasten x) _ [] = [] , [] , refl
F-incremental (hasten x) eq (_∷_ x' {xs' = xs'} pf)
  with yes refl ← x ≟ x'
  rewrite just-injective eq =
    xs' , pf , refl
F-incremental (e ⟫ e') {xs} eq {xs'} pfx
  with just ys ← F⟦ e ⟧ xs in eq₁
  with ys' , pfy , eq₂ ← F-incremental e eq₁ pfx
  with just zs ← F⟦ e' ⟧ ys in eq₃
  with zs' , pfz , eq₄ ← F-incremental e' eq₃ pfy
  rewrite sym (just-injective eq) | eq₂ | eq₄ =
    zs' , pfz , refl
F-incremental (e ⊗ e') {xzs} eq {xzs'} pfxz
  with xs' , zs' ← unzip xzs' in eq₁
  with xs , zs ← unzip xzs in eq₂
  with pfx , pfz ← ≺-unzip pfxz eq₁ eq₂
  with just ys ← F⟦ e ⟧ xs in eq₃
  with just ws ← F⟦ e' ⟧ zs in eq₄
  with ys' , pfy , eq₅ ← F-incremental e eq₃ pfx
  with ws' , pfw , eq₆ ← F-incremental e' eq₄ pfz
  rewrite sym (just-injective eq) | eq₅ | eq₆ =
    zip ys' ws' , ≺-zip pfy pfw , refl


B-incremental : ∀ (e : E X Y) → IsIncremental B⟦ e ⟧
B-incremental (map-fold {A} a f g) = B-map-fold-incremental a
  where
    B-map-fold-incremental : (a : A) → IsIncremental B⟦ map-fold a f g ⟧
    B-map-fold-incremental a eq [] = [] , [] , refl
    B-map-fold-incremental a eq (_∷_ y {xs = ys} pf)
      with just x ← f a .from y
      with just xs ← B-map-fold (g a x) f g ys in eq₁
      with xs' , pf' , eq₂ ← B-map-fold-incremental (g a x) eq₁ pf
      rewrite sym (just-injective eq) | eq₂ =
        x ∷ xs' , x ∷ pf' , refl
B-incremental (delay x) _ [] = [] , [] ,  refl
B-incremental (delay x) eq (_∷_ x' {xs' = xs} pf)
  with yes refl ← x ≟ x'
  rewrite just-injective eq =
    xs , pf , refl
B-incremental (hasten x) refl {xs'} pf = shift x xs' , ≺-shift x pf , refl
B-incremental (e ⟫ e') {zs} eq {zs'} pfz
  with just ys ← B⟦ e' ⟧ zs in eq₁
  with ys' , pfy , eq₂ ← B-incremental e' eq₁ pfz
  with just xs ← B⟦ e ⟧ ys in eq₃
  with xs' , pfx , eq₄ ← B-incremental e eq₃ pfy
  rewrite sym (just-injective eq) | eq₂ | eq₄ =
    xs' , pfx , refl
B-incremental (e ⊗ e') {yws} eq {yws'} pfyw
  with ys' , ws' ← unzip yws' in eq₁
  with ys , ws ← unzip yws in eq₂
  with pfy , pfw ← ≺-unzip pfyw eq₁ eq₂
  with just xs ← B⟦ e ⟧ ys in eq₃
  with just zs ← B⟦ e' ⟧ ws in eq₄
  with xs' , pfx , eq₅ ← B-incremental e eq₃ pfy
  with zs' , pfz , eq₆ ← B-incremental e' eq₄ pfw
  rewrite sym (just-injective eq) | eq₅ | eq₆ =
    zip xs' zs' , ≺-zip pfx pfz , refl


F-delay : ∀ (e : E X Y) → HasDelay DF⟦ e ⟧ F⟦ e ⟧
F-delay (map-fold {A} a f g) {xs} = F-map-fold-delay a {xs}
  where
    F-map-fold-delay : (a : A) → HasDelay 0 F⟦ map-fold a f g ⟧
    F-map-fold-delay a {[]} refl = refl
    F-map-fold-delay a {x ∷ xs} eq
      with just y ← f a .to x
      with just ys ← F-map-fold (g a x) f g xs in eq₁
      with ih ← F-map-fold-delay (g a x) {xs} eq₁
      rewrite sym (just-injective eq) =
        cong suc ih
F-delay (delay x) {xs} refl = length-shift x xs
F-delay (hasten x) {[]} refl = refl
F-delay (hasten x) {x' ∷ xs} eq
  with yes refl ← x ≟ x'
  rewrite sym (just-injective eq) =
    refl
F-delay (e ⟫ e') {xs} eq
  with just ys ← F⟦ e ⟧ xs in eq₁
  with ih₁ ← F-delay e eq₁
  with just zs ← F⟦ e' ⟧ ys in eq₂
  with ih₂ ← F-delay e' eq₂
  rewrite sym (just-injective eq) | ih₁ | ih₂ =
    ∸-+-assoc (length xs) DF⟦ e ⟧ DF⟦ e' ⟧
F-delay (e ⊗ e') {xzs} eq
  with xs , zs ← unzip xzs in eq₁
  with just ys ← F⟦ e ⟧ xs in eq₂
  with just ws ← F⟦ e' ⟧ zs in eq₃
  with ih₁ ← F-delay e eq₂
  with ih₂ ← F-delay e' eq₃
  rewrite sym (just-injective eq) | length-zipWith _,_ ys ws | ih₁ | ih₂
  with eq₄ , eq₅ ← length-unzip eq₁
  rewrite sym eq₄ | sym eq₅ =
    sym (∸-distribˡ-⊔-⊓ (length xzs) DF⟦ e ⟧ DF⟦ e' ⟧)

B-delay : ∀ (e : E X Y) → HasDelay DB⟦ e ⟧ B⟦ e ⟧
B-delay (map-fold {A} a f g) {ys} = B-map-fold-delay a {ys}
  where
    B-map-fold-delay : (a : A) → HasDelay 0 B⟦ map-fold a f g ⟧
    B-map-fold-delay a {[]} refl = refl
    B-map-fold-delay a {y ∷ ys} eq
      with just x ← f a .from y
      with just xs ← B-map-fold (g a x) f g ys in eq₁
      with ih ← B-map-fold-delay (g a x) {ys} eq₁
      rewrite sym (just-injective eq) =
        cong suc ih
B-delay (delay x) {[]} refl = refl
B-delay (delay x) {x' ∷ xs} eq
  with yes refl ← x ≟ x'
  rewrite sym (just-injective eq) =
    refl
B-delay (hasten x) {xs} refl = length-shift x xs
B-delay (e ⟫ e') {zs} eq
  with just ys ← B⟦ e' ⟧ zs in eq₁
  with ih₁ ← B-delay e' eq₁
  with just xs ← B⟦ e ⟧ ys in eq₂
  with ih₂ ← B-delay e eq₂
  rewrite sym (just-injective eq) | ih₁ | ih₂ =
    ∸-+-assoc (length zs) DB⟦ e' ⟧ DB⟦ e ⟧
B-delay (e ⊗ e') {yws} eq
  with ys , ws ← unzip yws in eq₁
  with just xs ← B⟦ e ⟧ ys in eq₂ | just zs ← B⟦ e' ⟧ ws in eq₃
  with ih₁ ← B-delay e eq₂
  with ih₂ ← B-delay e' eq₃
  rewrite sym (just-injective eq) | length-zipWith _,_ xs zs | ih₁ | ih₂
  with eq₄ , eq₅ ← length-unzip eq₁
  rewrite sym eq₄ | sym eq₅ =
    sym (∸-distribˡ-⊔-⊓ (length yws) DB⟦ e ⟧ DB⟦ e' ⟧)


F-IIST : ∀ (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (map-fold {A = A} a f g) = F-map-fold-IIST a
  where
    F-map-fold-IIST : (a : A) → F⟦ map-fold a f g ⟧ IsIISTOf B⟦ map-fold a f g ⟧
    F-map-fold-IIST a {[]} refl = [] , [] , refl
    F-map-fold-IIST a {y ∷ ys} eq
      with just x ← f a .from y in eq₁
      with just xs ← B-map-fold (g a x) f g ys in eq₂
      rewrite sym (just-injective eq) | f a .from→to eq₁
      with ys' , pf , eq₃ ← F-map-fold-IIST (g a x) {ys} eq₂
      rewrite eq₃ =
        y ∷ ys' , y ∷ pf , refl
F-IIST (delay x) {[]} refl = [] , [] , refl
F-IIST (delay x) {x' ∷ xs} eq
  with yes refl ← x ≟ x'
  rewrite sym (just-injective eq) =
    shift x' xs , shift-≺-∷ x xs , refl
F-IIST (hasten x) {[]} refl = [] , [] , refl
F-IIST (hasten x) {x' ∷ xs} refl with x ≟ x
... | no contra with () ← contra refl
... | yes refl = shift x' xs , shift-≺-∷ x' xs , refl
F-IIST (e ⟫ e') {zs} {xs} eq
  with just ys ← B⟦ e' ⟧ zs in eq₁
  with zs' , pfz , eq₁ ← F-IIST e' eq₁
  with just xs ← B⟦ e ⟧ ys in eq₂
  with ys' , pfy , eq₂ ← F-IIST e eq₂
  with zs'' , pfz' , eq₃ ← F-incremental e' eq₁ pfy
  rewrite sym (just-injective eq) | eq₁ | eq₂ =
    zs'' , ≺-trans pfz' pfz , eq₃
F-IIST (e ⊗ e') {yws} eq
  with ys , ws ← unzip yws in eq₁
  with just xs ← B⟦ e ⟧ ys in eq₂
  with just zs ← B⟦ e' ⟧ ws in eq₃
  with ys' , pfy , eq₂ ← F-IIST e eq₂
  with ws' , pfw , eq₃ ← F-IIST e' eq₃
  rewrite sym (just-injective eq)
  with xs' , zs' ← unzip (zip xs zs) in eq₄
  with pfx , pfz ← ≺-zip-unzip eq₄
  with ys'' , pfy' , eq₅ ← F-incremental e eq₂ pfx
  with ws'' , pfw' , eq₆ ← F-incremental e' eq₃ pfz
  rewrite sym (zip-unzip eq₁) | eq₅ | eq₆ =
    zip ys'' ws'' , ≺-zip (≺-trans pfy' pfy) (≺-trans pfw' pfw) , refl

B-IIST : ∀ (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (map-fold {A = A} a f g) = B-map-fold-IIST a
  where
    B-map-fold-IIST : (a : A) → B⟦ map-fold a f g ⟧ IsIISTOf F⟦ map-fold a f g ⟧
    B-map-fold-IIST a {[]} refl = [] , [] , refl
    B-map-fold-IIST a {x ∷ xs} eq
      with just y ← f a .to x in eq₁
      with just ys ← F-map-fold (g a x) f g xs in eq₂
      rewrite sym (just-injective eq) | f a .to→from eq₁
      with xs' , pf , eq₃ ← B-map-fold-IIST (g a x) {xs} eq₂
      rewrite eq₃ =
        x ∷ xs' , x ∷ pf , refl
B-IIST (delay x) {[]} refl = [] , [] , refl
B-IIST (delay x) {x' ∷ xs} refl with x ≟ x
... | no contra with () ← contra refl
... | yes refl = shift x' xs , shift-≺-∷ x' xs , refl
B-IIST (hasten x) {[]} refl = [] , [] , refl
B-IIST (hasten x) {x' ∷ xs} eq
  with yes refl ← x ≟ x'
  rewrite sym (just-injective eq) =
    shift x' xs , shift-≺-∷ x xs , refl
B-IIST (e ⟫ e') {xs} {zs} eq
  with just ys ← F⟦ e ⟧ xs in eq₁
  with xs' , pfx , eq₁ ← B-IIST e eq₁
  with just zs ← F⟦ e' ⟧ ys in eq₂
  with ys' , pfy , eq₂ ← B-IIST e' eq₂
  with xs'' , pfx' , eq₃ ← B-incremental e eq₁ pfy
  rewrite sym (just-injective eq) | eq₁ | eq₂ =
    xs'' , ≺-trans pfx' pfx , eq₃
B-IIST (e ⊗ e') {xzs} eq
  with xs , zs ← unzip xzs in eq₁
  with just ys ← F⟦ e ⟧ xs in eq₂
  with just ws ← F⟦ e' ⟧ zs in eq₃
  with xs' , pfx , eq₂ ← B-IIST e eq₂
  with zs' , pfz , eq₃ ← B-IIST e' eq₃
  rewrite sym (just-injective eq)
  with ys' , ws' ← unzip (zip ys ws) in eq₄
  with pfy , pfw ← ≺-zip-unzip eq₄
  with xs'' , pfx' , eq₅ ← B-incremental e eq₂ pfy
  with zs'' , pfz' , eq₆ ← B-incremental e' eq₃ pfw
  rewrite sym (zip-unzip eq₁) | eq₅ | eq₆ =
    zip xs'' zs'' , ≺-zip (≺-trans pfx' pfx) (≺-trans pfz' pfz) , refl


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


F∘I≡B : ∀ (e : E X Y) (ys : List Y) → F⟦ I⟦ e ⟧ ⟧ ys ≡ B⟦ e ⟧ ys
F∘I≡B {Y = Y} (map-fold {A} a f g) = F∘I≡B-map-fold a
  where
    F∘I≡B-map-fold : ∀ (a : A) (ys : List Y)
      → F⟦ I⟦ map-fold a f g ⟧ ⟧ ys ≡ B⟦ map-fold a f g ⟧ ys
    F∘I≡B-map-fold a [] = refl
    F∘I≡B-map-fold a (y ∷ ys) with f a .from y in eq
    ... | nothing = refl
    ... | just x rewrite f a .from→to eq | F∘I≡B-map-fold (g a x) ys = refl
F∘I≡B (delay x) [] = refl
F∘I≡B (delay x) (x' ∷ xs) with x ≟ x'
... | no _ = refl
... | yes refl = refl
F∘I≡B (hasten x) xs = refl
F∘I≡B (e ⟫ e') zs rewrite F∘I≡B e' zs with B⟦ e' ⟧ zs
... | nothing = refl
... | just ys = F∘I≡B e ys
F∘I≡B (e ⊗ e') xzs
  with xs , zs ← unzip xzs
  rewrite F∘I≡B e xs | F∘I≡B e' zs =
    refl

B∘I≡F : ∀ (e : E X Y) (xs : List X) → B⟦ I⟦ e ⟧ ⟧ xs ≡ F⟦ e ⟧ xs
B∘I≡F {X} (map-fold {A} a f g) = B∘I≡F-map-fold a
  where
    B∘I≡F-map-fold : ∀ (a : A) (xs : List X)
      → B⟦ I⟦ map-fold a f g ⟧ ⟧ xs ≡ F⟦ map-fold a f g ⟧ xs
    B∘I≡F-map-fold a [] = refl
    B∘I≡F-map-fold a (x ∷ xs) with f a .to x in eq
    ... | nothing = refl
    ... | just y rewrite f a .to→from eq | B∘I≡F-map-fold (g a x) xs = refl
B∘I≡F (delay x) xs = refl
B∘I≡F (hasten x) [] = refl
B∘I≡F (hasten x) (x' ∷ xs) with x ≟ x'
... | no _ = refl
... | yes refl = refl
B∘I≡F (e ⟫ e') xs rewrite B∘I≡F e xs with F⟦ e ⟧ xs
... | nothing = refl
... | just ys = B∘I≡F e' ys
B∘I≡F (e ⊗ e') xzs
  with xs , zs ← unzip xzs
  rewrite B∘I≡F e xs | B∘I≡F e' zs =
    refl
