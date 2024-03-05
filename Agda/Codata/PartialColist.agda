{-# OPTIONS --guardedness --cubical #-}

module Codata.PartialColist where

open import Cubical.Foundations.Everything
open import Cubical.Data.Empty.Base as Empty using () renaming ( ⊥ to Empty )
open import Cubical.Data.Sigma.Base using ( _×_; _,_; fst; snd )
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc )
open import Cubical.Data.List.Base using ( List; []; _∷_ )
open import Cubical.Data.Unit.Base using ( Unit; tt )
open import Relation.Binary.Bundles using ( Preorder )
open import Relation.Binary.Structures using ( IsPreorder )

open import Codata.PartialConat using ( Coℕ⊥; zero; ⊥; suc; force; _⊓_ )

private
  variable
    A B : Type

postulate sorry : A

--------------------------------------------------------------------------------
-- Partial Colist

infixr 5 _∷_

mutual

  data Colist⊥ (A : Type) : Type where
    [] : Colist⊥ A
    ⊥ : Colist⊥ A
    _∷_ : (x : A) (xs : ∞Colist⊥ A) → Colist⊥ A

  record ∞Colist⊥ (A : Type) : Type where
    coinductive
    constructor delay
    field force : Colist⊥ A

open ∞Colist⊥ public

-- η is safe for ∞Colist⊥
{-# ETA ∞Colist⊥ #-}

fromList : List A → Colist⊥ A
fromList [] = []
fromList (x ∷ xs) = x ∷ delay (fromList xs)

colength : Colist⊥ A → Coℕ⊥
colength [] = zero
colength ⊥ = ⊥
colength (_ ∷ xs) = suc λ where .force → colength (force xs)

map : (A → B) → Colist⊥ A → Colist⊥ B
map f [] = []
map f ⊥ = ⊥
map f (x ∷ xs) = f x ∷ λ where .force → map f (force xs)

zip : Colist⊥ A → Colist⊥ B → Colist⊥ (A × B)
zip ⊥ _ = ⊥
zip _ ⊥ = ⊥
zip [] _ = []
zip _ [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ λ where .force → zip (force xs) (force ys)

unzipₗ : Colist⊥ (A × B) → Colist⊥ A
unzipᵣ : Colist⊥ (A × B) → Colist⊥ B
unzipₗ = map fst
unzipᵣ = map snd

--------------------------------------------------------------------------------
-- Properties

colength-map : ∀ (f : A → B) xs → colength (map f xs) ≡ colength xs
colength-map f [] = refl
colength-map f ⊥ = refl
colength-map f (x ∷ xs) i = suc λ where .force → colength-map f (force xs) i

colength-zip : ∀ {xs : Colist⊥ A} {ys : Colist⊥ B}
  → colength (zip xs ys) ≡ (colength xs ⊓ colength ys)
colength-zip {xs = []} {[]} = refl
colength-zip {xs = []} {⊥} = refl
colength-zip {xs = []} {_ ∷ _} = refl
colength-zip {xs = ⊥} {[]} = refl
colength-zip {xs = ⊥} {⊥} = refl
colength-zip {xs = ⊥} {_ ∷ _} = refl
colength-zip {xs = _ ∷ _} {[]} = refl
colength-zip {xs = _ ∷ _} {⊥} = refl
colength-zip {xs = x ∷ xs} {y ∷ ys} i = suc λ where .force → colength-zip {xs = force xs} {ys = force ys} i

colength-unzipₗ : ∀ {xs : Colist⊥ (A × B)} → colength (unzipₗ xs) ≡ colength xs
colength-unzipᵣ : ∀ {xs : Colist⊥ (A × B)} → colength (unzipᵣ xs) ≡ colength xs
colength-unzipₗ = colength-map _ _
colength-unzipᵣ = colength-map _ _

unzip-zip : ∀ {xys : Colist⊥ (A × B)} → zip (unzipₗ xys) (unzipᵣ xys) ≡ xys
unzip-zip {xys = []} = refl
unzip-zip {xys = ⊥} = refl
unzip-zip {xys = xy ∷ xys} i = xy ∷ λ where .force → unzip-zip {xys = force xys} i

zip-⊥ᵣ : ∀ {xs} → Path (Colist⊥ (A × B)) (zip xs ⊥) ⊥
zip-⊥ᵣ {xs = []} = refl
zip-⊥ᵣ {xs = ⊥} = refl
zip-⊥ᵣ {xs = _ ∷ _} = refl

-------------------------------------------------------------------------------
-- Prefix

infix 4 _≺_ _≺≺_

data PrefixKind : Type where
  ⊥≺⊥ ⊥≺ : PrefixKind

mutual

  data Prefix {A} : PrefixKind → Colist⊥ A → Colist⊥ A → Type where
    con : ∀ {k xs ys} → Prefix′ k xs ys → Prefix k xs ys

  Prefix′ : PrefixKind → Colist⊥ A → Colist⊥ A → Type
  Prefix′ k [] ys = Unit
  Prefix′ ⊥≺⊥ ⊥ ⊥ = Unit
  Prefix′ ⊥≺ ⊥ ys = Unit
  Prefix′ k (x ∷ xs) (y ∷ ys) = (x ≡ y) × ∞Prefix k xs ys
  Prefix′ k xs ys = Empty

  record ∞Prefix k (xs ys : ∞Colist⊥ A) : Type where
    coinductive
    field force : Prefix k (force xs) (force ys)

open ∞Prefix public

_≺_ _≺≺_ : Colist⊥ A → Colist⊥ A → Type
_≺_ = Prefix ⊥≺⊥
_≺≺_ = Prefix ⊥≺

prefix-refl : ∀ {k} {xs : Colist⊥ A} → Prefix k xs xs
prefix-refl {xs = []} = con tt
prefix-refl {k = ⊥≺⊥} {xs = ⊥} = con tt
prefix-refl {k = ⊥≺} {xs = ⊥} = con tt
prefix-refl {xs = x ∷ xs} = con (refl , λ where .force → prefix-refl)

≡-to-prefix : ∀ {k} {xs ys : Colist⊥ A} → xs ≡ ys → Prefix k xs ys
≡-to-prefix eq = subst (Prefix _ _) eq prefix-refl

prefix-trans : ∀ {k} {xs ys zs : Colist⊥ A}
  → Prefix k xs ys
  → Prefix k ys zs
  → Prefix k xs zs
prefix-trans {xs = []} {ys} {zs} p q = con tt
prefix-trans {k = ⊥≺⊥} {xs = ⊥} {⊥} {⊥} p q = con tt
prefix-trans {k = ⊥≺} {xs = ⊥} {ys} {zs} p q = con tt
prefix-trans {xs = x ∷ xs} {y ∷ ys} {z ∷ zs} (con (p , p')) (con (q , q')) =
  con (p ∙ q , λ where .force → prefix-trans (force p') (force q'))
prefix-trans {xs = x ∷ xs} {[]} {zs} (con ()) q
prefix-trans {xs = xs} {y ∷ ys} {[]} p (con ())
prefix-trans {k = ⊥≺⊥} {xs = ⊥} {[]} {zs} (con ()) q
prefix-trans {k = ⊥≺⊥} {xs = ⊥} {y ∷ ys} {zs} (con ()) q
prefix-trans {k = ⊥≺⊥} {xs = xs} {⊥} {[]} p (con ())
prefix-trans {k = ⊥≺⊥} {xs = xs} {⊥} {z ∷ zs} p (con ())
prefix-trans {xs = x ∷ xs} {⊥} {zs} (con ()) q
prefix-trans {xs = xs} {ys = y ∷ ys} {⊥} p (con ())

prefix-isPreorder : ∀ {A k} → IsPreorder _≡_ (Prefix {A} k)
prefix-isPreorder = record
  { isEquivalence = record { refl = refl; sym = sym; trans = _∙_ }
  ; reflexive = ≡-to-prefix
  ; trans = prefix-trans
  }

prefix-preorder : ∀ {A k} → Preorder _ _ _
prefix-preorder {A} {k} = record { isPreorder = prefix-isPreorder {A} {k} }

module PrefixReasoning {A k} where
  open import Relation.Binary.Reasoning.Preorder (prefix-preorder {A} {k}) public

prefix-cong-zip : ∀ {k} {xs' xs : Colist⊥ A} {ys' ys : Colist⊥ B}
  → Prefix k xs' xs
  → Prefix k ys' ys
  → Prefix k (zip xs' ys') (zip xs ys)
prefix-cong-zip = sorry
-- prefix-cong-zip {k = ⊥≺⊥} {xs' = ⊥} {⊥} {ys'} {ys} p q = con tt
-- prefix-cong-zip {k = ⊥≺} {xs' = ⊥} {xs} {ys'} {ys} p q = con tt
-- prefix-cong-zip {k = ⊥≺⊥} {xs' = []} {[]} {⊥} {⊥} p q = con tt
-- prefix-cong-zip {k = ⊥≺⊥} {xs' = _ ∷ _} {_ ∷ _} {⊥} {⊥} p q = con tt
-- prefix-cong-zip {k = ⊥≺} {xs' = []} {[]} {⊥} {ys} p q = con tt
-- prefix-cong-zip {k = ⊥≺} {xs' = _ ∷ _} {_ ∷ _} {⊥} {ys} p q = con tt
-- prefix-cong-zip {xs' = []} {xs} {[]} {ys} p q = con tt
-- prefix-cong-zip {xs' = []} {xs} {_ ∷ _} {ys} p q = con tt
-- prefix-cong-zip {xs' = _ ∷ _} {xs} {[]} {ys} p q = con tt
-- prefix-cong-zip {xs' = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} (con (p , p')) (con (q , q')) =
--   con (cong₂ _,_ p q , λ where .force → prefix-cong-zip (force p') (force q'))
-- prefix-cong-zip {k = ⊥≺⊥} {xs' = ⊥} {[]} {ys'} {ys} (con ()) q
-- prefix-cong-zip {k = ⊥≺⊥} {xs' = ⊥} {x ∷ xs} {ys'} {ys} (con ()) q
-- prefix-cong-zip {xs' = xs'} {xs} {ys'} {ys} p q = {! xs' xs ys' ys  !}
-- prefix-cong-zip ⊥ _ = ⊥
-- prefix-cong-zip ⊥ₗ _ = ⊥ₗ
-- prefix-cong-zip {xs = []} [] ⊥ = ⊥
-- prefix-cong-zip {xs = ⊥} [] ⊥ = ⊥
-- prefix-cong-zip {xs = x ∷ xs} [] ⊥ = ⊥
-- prefix-cong-zip (_ ∷ _) ⊥ = ⊥
-- prefix-cong-zip [] ⊥ₗ = ⊥ₗ
-- prefix-cong-zip (_ ∷ _) ⊥ₗ = ⊥ₗ
-- prefix-cong-zip [] [] = []
-- prefix-cong-zip [] (_ ∷ _) = []
-- prefix-cong-zip (x ∷ p) [] = []
-- prefix-cong-zip (x ∷ p) (y ∷ q) = (x , y) ∷ λ where .force → prefix-cong-zip (force p) (force q)

prefix-cong-map : ∀ (f : A → B) {k} {xs' xs : Colist⊥ A}
  → Prefix k xs' xs
  → Prefix k (map f xs') (map f xs)
prefix-cong-map f {xs' = []} {xs} p = con tt
prefix-cong-map f {k = ⊥≺⊥} {xs' = ⊥} {[]} (con ())
prefix-cong-map f {k = ⊥≺⊥} {xs' = ⊥} {⊥} (con tt) = con tt
prefix-cong-map f {k = ⊥≺⊥} {xs' = ⊥} {x ∷ xs} (con ())
prefix-cong-map f {k = ⊥≺} {xs' = ⊥} {xs} (con tt) = con tt
prefix-cong-map f {xs' = x' ∷ xs'} {[]} (con ())
prefix-cong-map f {xs' = x' ∷ xs'} {⊥} (con ())
prefix-cong-map f {xs' = x' ∷ xs'} {x ∷ xs} (con (p , q)) =
  con (cong f p , λ where .force → prefix-cong-map f (force q))

prefix-cong-unzipₗ : ∀ {k} {xys' xys : Colist⊥ (A × B)}
  → Prefix k xys' xys
  → Prefix k (unzipₗ xys') (unzipₗ xys)
prefix-cong-unzipₗ = prefix-cong-map fst

prefix-cong-unzipᵣ : ∀ {k} {xys' xys : Colist⊥ (A × B)}
  → Prefix k xys' xys
  → Prefix k (unzipᵣ xys') (unzipᵣ xys)
prefix-cong-unzipᵣ = prefix-cong-map snd

zip-unzipₗ : ∀ (xs : Colist⊥ A) (ys : Colist⊥ B) → unzipₗ (zip xs ys) ≺≺ xs
zip-unzipₗ [] [] = con tt
zip-unzipₗ [] ⊥ = con tt
zip-unzipₗ [] (x ∷ xs) = (con tt)
zip-unzipₗ ⊥ ys = (con tt)
zip-unzipₗ (x ∷ xs) [] = con tt
zip-unzipₗ (x ∷ xs) ⊥ = con tt
zip-unzipₗ (x ∷ xs) (y ∷ ys) = con (refl , λ where .force → zip-unzipₗ (force xs) (force ys))

zip-unzipᵣ : ∀ (xs : Colist⊥ A) (ys : Colist⊥ B) → unzipᵣ (zip xs ys) ≺≺ ys
zip-unzipᵣ [] [] = con tt
zip-unzipᵣ [] ⊥ = con tt
zip-unzipᵣ [] (x ∷ xs) = con tt
zip-unzipᵣ ⊥ ys = con tt
zip-unzipᵣ (x ∷ xs) [] = con tt
zip-unzipᵣ (x ∷ xs) ⊥ = con tt
zip-unzipᵣ (x ∷ xs) (y ∷ ys) = con (refl , λ where .force → zip-unzipᵣ (force xs) (force ys))
