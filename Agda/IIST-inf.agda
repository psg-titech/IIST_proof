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
shift x fail = x ∷ λ where .force → fail
shift x (y ∷ xs) = x ∷ λ where .force → shift y (force xs)

unshift : {{_ : Eq A}} → A → Colistˣ A → Colistˣ A
unshift x [] = []
unshift x fail = fail
unshift x (y ∷ xs) with x ≟ y
... | no _ = fail
... | yes _ = force xs

-------------------------------------------------------------------------------
-- Prefix

shift-≺-∷ : ∀ (x : A) xs → (shift x xs) ≺ (x ∷ delay xs)
shift-≺-∷ x [] = []
shift-≺-∷ x fail = x ∷ λ where .force → fail
shift-≺-∷ x (y ∷ xs) = x ∷ λ where .force → shift-≺-∷ y (force xs)

≺-shift : ∀ (x : A) {xs ys} → xs ≺ ys → shift x xs ≺ shift x ys
≺-shift x [] = []
≺-shift x fail = x ∷ λ where .force → fail
≺-shift x (y ∷ xs≺ys) = x ∷ λ where .force → ≺-shift y (force xs≺ys)

≺-unshift : ∀ {{_ : Eq A}} (x : A) {xs ys} → xs ≺ ys → unshift x xs ≺ unshift x ys
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
IsIncremental st = ∀ {xs xs'} → xs' ≺ xs → st xs' ≺ st xs

HasDelay : ℕ → ST X Y → Set
HasDelay d st = ∀ {xs}
  → Colistˣ.NoFail (st xs)
  → colength (st xs) Coℕˣ.≈ (colength xs ∸ℕ d)

record Is_-IST_ (d : ℕ) (st : ST X Y) : Set where
  field
    empty : st [] ≡ []
    isIncremental : IsIncremental st
    hasDelay : HasDelay d st

_IsIISTOf_ : ST X Y → ST Y X → Set
st' IsIISTOf st = ∀ {xs}
  → Colistˣ.NoFail (st xs)
  → st' (st xs) ≺ xs

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
-- No fail

map-arg-noFail : ∀ (f : A → B) {xs : Colistˣ A}
  → NoFail (map f xs)
  → NoFail xs
map-arg-noFail f {[]} [] = []
map-arg-noFail f {x ∷ xs} (.(f x) ∷ nf) = x ∷ λ where .force → map-arg-noFail f (force nf)

unzipₗ-arg-noFail : ∀ {xzs : Colistˣ (A × B)} → NoFail (unzipₗ xzs) → NoFail xzs
unzipₗ-arg-noFail = map-arg-noFail proj₁

unzipᵣ-arg-noFail : ∀ {xzs : Colistˣ (A × B)} → NoFail (unzipᵣ xzs) → NoFail xzs
unzipᵣ-arg-noFail = map-arg-noFail proj₂

unzip-zip-arg-noFail : ∀ {xzs : Colistˣ (X × Z)} {st : ST X Y} {st' : ST Z W}
  → (∀ {xs : Colistˣ X} → NoFail (st xs) → NoFail xs)
  → (∀ {zs : Colistˣ Z} → NoFail (st' zs) → NoFail zs)
  → NoFail (zip (st (unzipₗ xzs)) (st' (unzipᵣ xzs)))
  → NoFail xzs
unzip-zip-arg-noFail = {!   !}

shift-arg-noFail : ∀ {{_ : Eq X}} (x : X) {xs} → NoFail (shift x xs) → NoFail xs
shift-arg-noFail x {[]} [] = []
shift-arg-noFail x {fail} (.x ∷ nf) with () ← force nf
shift-arg-noFail x {y ∷ xs} (.x ∷ nf) = y ∷ λ where .force → shift-arg-noFail y (force nf)

unshift-arg-noFail : ∀ {{_ : Eq X}} (x : X) {xs} → NoFail (unshift x xs) → NoFail xs
unshift-arg-noFail x {[]} [] = []
unshift-arg-noFail x {y ∷ xs} nf with x ≟ y
unshift-arg-noFail x {y ∷ xs} () | no _
unshift-arg-noFail x {y ∷ xs} nf | yes refl = x ∷ λ where .force → nf

F-arg-noFail : ∀ (e : E X Y) {xs} → NoFail (F⟦ e ⟧ xs) → NoFail xs
F-arg-noFail (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) {ys} → NoFail (F⟦ map-fold a f g ⟧ ys) → NoFail ys
    helper a {[]} [] = []
    helper a {x ∷ xs} nf with f a .to x
    helper a {x ∷ xs} () | nothing
    helper a {x ∷ xs} (.y ∷ nf) | just y = x ∷ λ where .force → helper (g a x) (force nf)
F-arg-noFail (delay x) = shift-arg-noFail x
F-arg-noFail (hasten x) = unshift-arg-noFail x
F-arg-noFail (e ⟫ e') = F-arg-noFail e ∘ F-arg-noFail e'
F-arg-noFail (e ⊗ e') = unzip-zip-arg-noFail (F-arg-noFail e) (F-arg-noFail e')

B-arg-noFail : ∀ (e : E X Y) {ys} → NoFail (B⟦ e ⟧ ys) → NoFail ys
B-arg-noFail (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) {ys} → NoFail (B⟦ map-fold a f g ⟧ ys) → NoFail ys
    helper a {[]} [] = []
    helper a {y ∷ ys} nf with f a .from y
    helper a {y ∷ ys} () | nothing
    helper a {y ∷ ys} (.x ∷ nf) | just x = y ∷ λ where .force → helper (g a x) (force nf)
B-arg-noFail (delay x) = unshift-arg-noFail x
B-arg-noFail (hasten x) = shift-arg-noFail x
B-arg-noFail (e ⟫ e') = B-arg-noFail e' ∘ B-arg-noFail e
B-arg-noFail (e ⊗ e') = unzip-zip-arg-noFail (B-arg-noFail e) (B-arg-noFail e')

--------------------------------------------------------------------------------
-- d-Incrementality of F⟦_⟧ and B⟦_⟧

shift-colength : ∀ (x : A) {xs} (nf : NoFail (shift x xs))
  → colength (shift x xs) Coℕˣ.≈ colength xs
shift-colength x {[]} [] = ≈zero
shift-colength x {fail} (.x ∷ nf) with () ← force nf
shift-colength x {y ∷ _} (.x ∷ nf) = ≈suc λ where .force → shift-colength y (force nf)

unshift-colength : ∀ {{_ : Eq A}} (x : A) {xs} (nf : NoFail (unshift x xs))
  → colength (unshift x xs) Coℕˣ.≈ colength xs ∸ℕ 1
unshift-colength x {[]} nf = ≈zero
unshift-colength x {y ∷ xs} nf with x ≟ y
unshift-colength x {y ∷ xs} () | no _
unshift-colength x {y ∷ xs} nf | yes _ = Coℕˣ.≈-refl

F-delay : ∀ (e : E X Y) → HasDelay DF⟦ e ⟧ F⟦ e ⟧
F-delay (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → HasDelay 0 F⟦ map-fold a f g ⟧
    helper a {[]} nf = ≈zero
    helper a {x ∷ xs} nf with f a .to x
    helper a {x ∷ xs} () | nothing
    helper a {x ∷ xs} (.y ∷ nf) | just y = ≈suc λ where .force → helper (g a x) (force nf)
F-delay (delay x) = shift-colength x
F-delay (hasten x) {xs} = unshift-colength x {xs}
F-delay (e ⟫ e') nf =
  let ih = F-delay e (F-arg-noFail e' nf)
      ih' = F-delay e' nf
  in Coℕˣ.≈-trans
       ih'
       (Coℕˣ.≈-trans
         (≈-∸ℕ DF⟦ e' ⟧ ih)
         (∸-+-assoc _ DF⟦ e ⟧ DF⟦  e' ⟧))
F-delay (e ⊗ e') nf = {!   !}

B-delay : ∀ (e : E X Y) → HasDelay DB⟦ e ⟧ B⟦ e ⟧
B-delay (map-fold {A} a f g) = helper a
  where
    helper : ∀ (a : A) → HasDelay 0 B⟦ map-fold a f g ⟧
    helper a {[]} nf = ≈zero
    helper a {y ∷ ys} nf with f a .from y
    helper a {y ∷ ys} () | nothing
    helper a {y ∷ ys} (.x ∷ nf) | just x = ≈suc λ where .force → helper (g a x) (force nf)
B-delay (delay x) {xs} = unshift-colength x {xs}
B-delay (hasten x) = shift-colength x
B-delay (e ⟫ e') nf =
  let ih = B-delay e' (B-arg-noFail e nf)
      ih' = B-delay e nf
  in Coℕˣ.≈-trans
       ih'
       (Coℕˣ.≈-trans
         (≈-∸ℕ DB⟦ e ⟧ ih)
         (∸-+-assoc _ DB⟦ e' ⟧ DB⟦  e ⟧))
B-delay (e ⊗ e') nf = {!   !}

--------------------------------------------------------------------------------
-- F⟦_⟧ and B⟦_⟧ are inverse of each other

shift-IIST : ∀ {{_ : Eq X}} (x : X) → shift x IsIISTOf unshift x
shift-IIST x {[]} nf = []
shift-IIST x {y ∷ xs} nf with x ≟ y
shift-IIST x {y ∷ xs} () | no _
shift-IIST x {y ∷ xs} nf | yes refl = shift-≺-∷ x (force xs)

unshift-IIST : ∀ {{_ : Eq X}} (x : X) → unshift x IsIISTOf shift x
unshift-IIST x {[]} nf = []
unshift-IIST x {fail} nf with x ≟ x
unshift-IIST x {fail} nf | no contra with () ← contra refl
unshift-IIST x {fail} nf | yes refl = fail
unshift-IIST x {y ∷ xs} nf with x ≟ x
unshift-IIST x {y ∷ xs} nf | no contra with () ← contra refl
unshift-IIST x {y ∷ xs} nf | yes refl = shift-≺-∷ y (force xs)

F-IIST : ∀ (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → F⟦ map-fold a f g ⟧ IsIISTOf B⟦ map-fold a f g ⟧
    helper a {[]} nf = []
    helper a {y ∷ ys} nf with f a .from y in eq
    helper a {y ∷ ys} () | nothing
    helper a {y ∷ ys} (_ ∷ nf) | just x rewrite f a .from→to eq =
      y ∷ λ where .force → helper (g a x) (force nf)
F-IIST (delay x) = shift-IIST x
F-IIST (hasten x) = unshift-IIST x
F-IIST (e ⟫ e') nf =
  let ih = F-IIST e nf
      ih' = F-IIST e' (B-arg-noFail e nf)
   in ≺-trans (F-incremental e' ih) ih'
F-IIST (e ⊗ e') = {!   !}

B-IIST : ∀ (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (map-fold {A} a f g) = helper a
  where
    helper : (a : A) → B⟦ map-fold a f g ⟧ IsIISTOf F⟦ map-fold a f g ⟧
    helper a {[]} nf = []
    helper a {x ∷ xs} nf with f a .to x in eq
    helper a {x ∷ xs} () | nothing
    helper a {x ∷ xs} (_ ∷ nf) | just y rewrite f a .to→from eq =
      x ∷ λ where .force → helper (g a x) (force nf)
B-IIST (delay x) = unshift-IIST x
B-IIST (hasten x) = shift-IIST x
B-IIST (e ⟫ e') {zs} nf =
  let ih = B-IIST e' nf
      ih' = B-IIST e (F-arg-noFail e' nf)
   in ≺-trans (B-incremental e ih) ih'
B-IIST (e ⊗ e') = {!   !}

{-

delay : failが未来に送られる
hasten : 失敗する
map-fold : 失敗する
_⊕_ : 長い方に失敗があっても短い方とzipすることで失敗しなくなる

ih   : B⟦ e ⟧  (F⟦ e ⟧ (unzipₗ yws)) ≺ unzipₗ yws
ih'  : B⟦ e' ⟧ (F⟦ e' ⟧ (unzipᵣ yws)) ≺ unzipᵣ yws
goal :
  zip
    (B⟦ e ⟧  (unzipₗ (zip (F⟦ e ⟧ (unzipₗ yws)) (F⟦ e' ⟧ (unzipᵣ yws)))))
    (B⟦ e' ⟧ (unzipᵣ (zip (F⟦ e ⟧ (unzipₗ yws)) (F⟦ e' ⟧ (unzipᵣ yws)))))
  ≺ yws

-}

--------------------------------------------------------------------------------
-- Bundles

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

--------------------------------------------------------------------------------
-- Properties of I⟦_⟧

≈-shift : ∀ (x : A) {xs ys} → xs Colistˣ.≈ ys → shift x xs Colistˣ.≈ shift x ys
≈-shift x ≈[] = ≈[]
≈-shift x ≈fail = refl ≈∷ λ where .force → ≈fail
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
