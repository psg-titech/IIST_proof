{-# OPTIONS --guardedness #-}

module Codata.FallibleColist where

open import Data.Product.Base using ( _×_; _,_; proj₁; proj₂ )
open import Data.Nat.Base using ( ℕ; zero; suc )
open import Relation.Binary.Bundles using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans )
open import Relation.Binary.Structures using ( IsEquivalence )

open import Codata.FallibleConat as Coℕˣ using ( Coℕˣ; zero; fail; suc; force; _⊓_ )

private
  variable
    A B : Set

infixr 5 _∷_

--------------------------------------------------------------------------------
-- Fallible Colist

mutual

  data Colistˣ (A : Set) : Set where
    [] : Colistˣ A
    fail : Colistˣ A
    _∷_ : A → ∞Colistˣ A → Colistˣ A

  record ∞Colistˣ (A : Set) : Set where
    coinductive
    constructor delay
    field force : Colistˣ A

open ∞Colistˣ public

-- η is safe for ∞Colistˣ
{-# ETA ∞Colistˣ #-}

colength : Colistˣ A → Coℕˣ
colength [] = zero
colength fail = fail
colength (_ ∷ xs) = suc λ where .force → colength (force xs)

drop : ℕ → Colistˣ A → Colistˣ A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) fail = fail
drop (suc n) (_ ∷ xs) = drop n (force xs)

map : (A → B) → Colistˣ A → Colistˣ B
map f [] = []
map f fail = fail
map f (x ∷ xs) = f x ∷ λ where .force → map f (force xs)

zip : Colistˣ A → Colistˣ B → Colistˣ (A × B)
zip fail _ = fail
zip _ fail = fail
zip [] _ = []
zip _ [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ λ where .force → zip (force xs) (force ys)

unzipₗ : Colistˣ (A × B) → Colistˣ A
unzipₗ = map proj₁

unzipᵣ : Colistˣ (A × B) → Colistˣ B
unzipᵣ = map proj₂

colength-map : ∀ (f : A → B) xs → colength (map f xs) Coℕˣ.≈ colength xs
colength-map f [] = zero
colength-map f fail = fail
colength-map f (x ∷ xs) = suc λ where .force → colength-map f (force xs)

colength-zip : ∀ {xs : Colistˣ A} {ys : Colistˣ B}
  → colength (zip xs ys) Coℕˣ.≈ (colength xs ⊓ colength ys)
colength-zip {xs = []} {[]} = zero
colength-zip {xs = []} {fail} = fail
colength-zip {xs = []} {_ ∷ _} = zero
colength-zip {xs = fail} {[]} = fail
colength-zip {xs = fail} {fail} = fail
colength-zip {xs = fail} {_ ∷ _} = fail
colength-zip {xs = _ ∷ _} {[]} = zero
colength-zip {xs = _ ∷ _} {fail} = fail
colength-zip {xs = x ∷ xs} {y ∷ ys} = suc λ where .force → colength-zip

colength-unzipₗ : ∀ {xs : Colistˣ (A × B)} → colength (unzipₗ xs) Coℕˣ.≈ colength xs
colength-unzipₗ = colength-map _ _

colength-unzipᵣ : ∀ {xs : Colistˣ (A × B)} → colength (unzipᵣ xs) Coℕˣ.≈ colength xs
colength-unzipᵣ = colength-map _ _

--------------------------------------------------------------------------------
-- No Fail

mutual

  data NoFail {A : Set} : Colistˣ A → Set where
    [] : NoFail []
    _∷_ : ∀ x {xs} → ∞NoFail xs → NoFail (x ∷ xs)

  record ∞NoFail (xs : ∞Colistˣ A) : Set where
    coinductive
    field force : NoFail (force xs)

open ∞NoFail public

noFail-map : ∀ (f : A → B) {xs} → NoFail xs → NoFail (map f xs)
noFail-map f [] = []
noFail-map f (x ∷ xs) = f x ∷ λ where .force → noFail-map f (force xs)

noFail-zip : ∀ {xs : Colistˣ A} {ys : Colistˣ B}
  → NoFail xs
  → NoFail ys
  → NoFail (zip xs ys)
noFail-zip [] [] = []
noFail-zip [] (_ ∷ _) = []
noFail-zip (_ ∷ _) [] = []
noFail-zip (x ∷ xs) (y ∷ ys) =
  (x , y) ∷ λ where .force → noFail-zip (force xs) (force ys)

--------------------------------------------------------------------------------
-- Bisimulation

infix 4 _≈_ _∞≈_

mutual

  data _≈_ {A : Set} : Colistˣ A → Colistˣ A → Set where
    [] : [] ≈ []
    fail : fail ≈ fail
    _∷_ : ∀ {x y xs ys} → x ≡ y → xs ∞≈ ys → (x ∷ xs) ≈ (y ∷ ys)

  record _∞≈_ (xs ys : ∞Colistˣ A) : Set where
    coinductive
    field force : force xs ≈ force ys

open _∞≈_ public

≈-refl : ∀ {xs : Colistˣ A} → xs ≈ xs
≈-refl {xs = []} = []
≈-refl {xs = fail} = fail
≈-refl {xs = x ∷ xs} = refl ∷ λ where .force → ≈-refl

≈-sym : ∀ {xs ys : Colistˣ A} → xs ≈ ys → ys ≈ xs
≈-sym [] = []
≈-sym fail = fail
≈-sym (x≡y ∷ xs≈ys) = sym x≡y ∷ λ where .force → ≈-sym (force xs≈ys)

≈-trans : ∀ {xs ys zs : Colistˣ A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans [] ys≈zs = ys≈zs
≈-trans fail ys≈zs = ys≈zs
≈-trans (x≡y ∷ xs≈ys) (y≡z ∷ ys≈zs) =
  trans x≡y y≡z ∷ λ where .force → ≈-trans (force xs≈ys) (force ys≈zs)


≈-isEquivalence : ∀ {A} → IsEquivalence {A = Colistˣ A} _≈_
≈-isEquivalence = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = ≈-trans
  }

≈-setoid : ∀ {A} → Setoid _ _
≈-setoid {A} = record { isEquivalence = ≈-isEquivalence {A} }

≈-map : ∀ {xs xs' : Colistˣ A} (f : A → B)
  → xs ≈ xs'
  → map f xs ≈ map f xs'
≈-map f [] = []
≈-map f fail = fail
≈-map f (refl ∷ xs≈xs') = refl ∷ λ where .force → ≈-map f (force xs≈xs')

≈-zip : ∀ {xs xs' : Colistˣ A} {ys ys' : Colistˣ B}
  → xs ≈ xs'
  → ys ≈ ys'
  → zip xs ys ≈ zip xs' ys'
≈-zip fail _ = fail
≈-zip [] fail = fail
≈-zip (_ ∷ _) fail = fail
≈-zip [] [] = []
≈-zip [] (_ ∷ _) = []
≈-zip (_ ∷ _) [] = []
≈-zip (refl ∷ xs≈xs') (refl ∷ ys≈ys') =
  refl ∷ λ where .force → ≈-zip (force xs≈xs') (force ys≈ys')

≈-unzipₗ : ∀ {xs xs' : Colistˣ (A × B)} → xs ≈ xs' → unzipₗ xs ≈ unzipₗ xs'
≈-unzipₗ = ≈-map _

≈-unzipᵣ : ∀ {xs xs' : Colistˣ (A × B)} → xs ≈ xs' → unzipᵣ xs ≈ unzipᵣ xs'
≈-unzipᵣ = ≈-map _

-------------------------------------------------------------------------------
-- Prefix

infix 4 _≺_ _∞≺_

mutual

  data _≺_ {A : Set} : Colistˣ A → Colistˣ A → Set where
    [] : ∀ {xs} → [] ≺ xs
    fail : fail ≺ fail
    _∷_ : ∀ x {xs ys} → xs ∞≺ ys → (x ∷ xs) ≺ (x ∷ ys)

  record _∞≺_ (xs ys : ∞Colistˣ A) : Set where
    coinductive
    field force : force xs ≺ force ys

open _∞≺_ public

≺-refl : ∀ {xs : Colistˣ A} → xs ≺ xs
≺-refl {xs = []} = []
≺-refl {xs = fail} = fail
≺-refl {xs = x ∷ xs} = x ∷ λ where .force → ≺-refl

≺-trans : ∀ {xs ys zs : Colistˣ A}
  → xs ≺ ys
  → ys ≺ zs
  → xs ≺ zs
≺-trans [] ys≺zs = []
≺-trans fail fail = fail
≺-trans (x ∷ xs≺ys) (.x ∷ ys≺zs) = x ∷ λ where .force → ≺-trans (force xs≺ys) (force ys≺zs)

≺-zip : ∀ {xs xs' : Colistˣ A} {ys ys' : Colistˣ B}
  → xs' ≺ xs
  → ys' ≺ ys
  → zip xs' ys' ≺ zip xs ys
≺-zip {xs = []} [] fail = fail
≺-zip {xs = fail} [] fail = fail
≺-zip {xs = _ ∷ _} [] fail = fail
≺-zip [] [] = []
≺-zip [] (_ ∷ _) = []
≺-zip {ys = []} fail [] = fail
≺-zip {ys = fail} fail [] = fail
≺-zip {ys = _ ∷ _} fail [] = fail
≺-zip fail fail = fail
≺-zip fail (_ ∷ _) = fail
≺-zip (x ∷ xs'≺xs) [] = []
≺-zip (x ∷ xs'≺xs) fail = fail
≺-zip (x ∷ xs'≺xs) (y ∷ ys'≺ys) = (x , y) ∷ λ where .force → ≺-zip (force xs'≺xs) (force ys'≺ys)

≺-unzipₗ : ∀ {xys' xys : Colistˣ (A × B)}
  → xys' ≺ xys
  → unzipₗ xys' ≺ unzipₗ xys
≺-unzipₗ [] = []
≺-unzipₗ fail = fail
≺-unzipₗ ((x , y) ∷ xys'≺xys) = x ∷ λ where .force → ≺-unzipₗ (force xys'≺xys)

≺-unzipᵣ : ∀ {xys' xys : Colistˣ (A × B)}
  → xys' ≺ xys
  → unzipᵣ xys' ≺ unzipᵣ xys
≺-unzipᵣ [] = []
≺-unzipᵣ fail = fail
≺-unzipᵣ ((x , y) ∷ xys'≺xys) = y ∷ λ where .force → ≺-unzipᵣ (force xys'≺xys)

-- ≺-zip-unzipₗ : ∀ (xs : Colistˣ A) (ys : Colistˣ B)
--   → unzipₗ (zip xs ys) ≺ xs
-- ≺-zip-unzipₗ [] [] = []
-- ≺-zip-unzipₗ [] fail = {!   !}
-- ≺-zip-unzipₗ [] (x ∷ xs) = []
-- ≺-zip-unzipₗ (fail) ys = fail
-- ≺-zip-unzipₗ (x ∷ xs) [] = []
-- ≺-zip-unzipₗ (x ∷ xs) fail = {!   !}
-- ≺-zip-unzipₗ (x ∷ xs) (y ∷ ys) = x ∷ λ where .force → ≺-zip-unzipₗ (force xs) (force ys)

--------------------------------------------------------------------------------
-- Properties
