module IIST where

open import Category.Monad using ( RawMonad )
open RawMonad {{...}} using ( _>>=_; return ) renaming ( _<=<_ to _∙_ )
open import Data.List using ( List; []; _∷_ )
open import Data.List.Properties using ( ≡-dec )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Maybe.Categorical using ( monad )
open import Data.Maybe.Relation.Unary.All using ( All; just; nothing )
open import Data.Nat using ( ℕ; zero; suc; _⊔_; _⊓_; _+_; _∸_; pred )
open import Data.Nat.Properties using ( _≟_ ; +-comm ; ∸-+-assoc ; ∸-distribˡ-⊓-⊔ ; ∸-distribˡ-⊔-⊓ )
open import Data.Product using ( _×_; _,_; proj₁; proj₂ )
open import Data.Vec using ( Vec; []; _∷_; unzip; restrict )
open import Function using ( _$_ )
open import Relation.Nullary using ( Dec; yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; cong; trans )

infix 0 _⇀_ _⇌_ _↔_
infixr 9 _⟫_
infixr 3 _⊗_

instance
  maybeMonad = monad

private
  variable
    n m d d' : ℕ
    A X Y Z W : Set

-------------------------------------------------------------------------------
-- Misc.

cast : .(m ≡ n) → Vec X m → Vec X n
cast {n = zero} eq [] = []
cast {n = suc _} eq (x ∷ xs) = x ∷ cast (cong pred eq) xs

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (Q → P)

-------------------------------------------------------------------------------
-- Partial function and Partial invertible function

_⇀_ : Set → Set → Set
X ⇀ Y = X → Maybe Y

record _⇌_ (X Y : Set) : Set where
  constructor invertible
  field
    to : X ⇀ Y
    from : Y ⇀ X
    proof : ∀ x y → to x ≡ just y ↔ from y ≡ just x

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
  _==_ {{eqNat}} = _≟_

  eqList : {{_ : Eq X}} → Eq (List X)
  _==_ {{eqList}} = ≡-dec _==_

-------------------------------------------------------------------------------
-- Syntax

data E : ℕ → ℕ → Set → Set → Set₁ where
  map-fold : A → (A → X ⇌ Y) → (A → X → A) → E 0 0 X Y
  delay : {{Eq X}} → X → E 0 1 X X
  hasten : {{Eq X}} → X → E 1 0 X X
  _⟫_ : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Y Z
    → E (d₁ + d₂) (d₁' + d₂') X Z
  _⊗_ : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Z W
    → E (d₁ ⊔ d₂) (d₁' ⊔ d₂') (X × Z) (Y × W)

-------------------------------------------------------------------------------
-- Semantics

_▻_ : X → Vec X n → Vec X n
_ ▻ [] = []
x ▻ (y ∷ v) = x ∷ y ▻ v

mutual

  -- Forward semantics
  F⟦_⟧_ : E d d' X Y → Vec X n ⇀ Vec Y (n ∸ d)
  F⟦ map-fold a f g ⟧ s = map-fold-forward a f g s
  F⟦ delay x ⟧ s = delay-forward x s
  F⟦ hasten x ⟧ s = hasten-forward x s
  F⟦ e ⟫ e' ⟧ s = ⟫-forward e e' s
  F⟦ e ⊗ e' ⟧ s = ⊗-forward e e' s

  map-fold-forward : A → (A → X ⇌ Y) → (A → X → A) → Vec X n ⇀ Vec Y n
  map-fold-forward a f g [] = return []
  map-fold-forward a f g (x ∷ xs) = do
    y ← f a .to x
    ys ← map-fold-forward (g a x) f g xs
    return $ y ∷ ys

  delay-forward : X → Vec X n ⇀ Vec X n
  delay-forward x s = return $ x ▻ s

  hasten-forward : {{Eq X}} → X → Vec X n ⇀ Vec X (n ∸ 1)
  hasten-forward x [] = return []
  hasten-forward x (y ∷ s) with x == y
  ... | yes refl = return s
  ... | no _ = nothing

  ⟫-forward : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Y Z
    → Vec X n ⇀ Vec Z (n ∸ (d₁ + d₂))
  ⟫-forward {n = n} {d₁ = d₁} {d₂ = d₂} e e' s = do
    s₁ ← F⟦ e ⟧ s
    s₂ ← F⟦ e' ⟧ s₁
    return $ cast (∸-+-assoc n d₁ d₂) s₂

  ⊗-forward : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Z W
    → Vec (X × Z) n ⇀ Vec (Y × W) (n ∸ (d₁ ⊔ d₂))
  ⊗-forward {n = n} {d₁ = d₁} {d₂ = d₂} e e' s with unzip s
  ... | s₁ , s₂ = do
        s₁' ← F⟦ e ⟧ s₁
        s₂' ← F⟦ e' ⟧ s₂
        return $ cast (sym $ ∸-distribˡ-⊔-⊓ n d₁ d₂) $ restrict s₁' s₂'

  -- Backward semantics
  B⟦_⟧_ : E d d' X Y → Vec Y n ⇀ Vec X (n ∸ d')
  B⟦ map-fold a f g ⟧ s = map-fold-backward a f g s
  B⟦ delay x ⟧ s = delay-backward x s
  B⟦ hasten x ⟧ s = hasten-backward x s
  B⟦ e ⟫ e' ⟧ s = ⟫-backward e e' s
  B⟦ e ⊗ e' ⟧ s = ⊗-backward e e' s

  map-fold-backward : A → (A → X ⇌ Y) → (A → X → A) → Vec Y n ⇀ Vec X n
  map-fold-backward a f g [] = just []
  map-fold-backward a f g (y ∷ ys) = do
    x ← f a .from y
    xs ← map-fold-backward (g a x) f g ys
    return $ x ∷ xs

  delay-backward = hasten-forward
  hasten-backward = delay-forward

  ⟫-backward : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Y Z
    → Vec Z n ⇀ Vec X (n ∸ (d₁' + d₂'))
  ⟫-backward {n = n} {d₁' = d₁'} {d₂' = d₂'} e e' s = do
    s₁ ← B⟦ e' ⟧ s
    s₂ ← B⟦ e ⟧ s₁
    return $ cast (trans (∸-+-assoc n d₂' d₁') (cong (n ∸_) (+-comm d₂' d₁'))) s₂

  ⊗-backward : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Z W
    → Vec (Y × W) n ⇀ Vec (X × Z) (n ∸ (d₁' ⊔ d₂'))
  ⊗-backward {n = n} {d₁' = d₁'} {d₂' = d₂'} e e' s with unzip s
  ... | s₁ , s₂ = do
        s₁' ← B⟦ e ⟧ s₁
        s₂' ← B⟦ e' ⟧ s₂
        return $ cast (sym $ ∸-distribˡ-⊔-⊓ n d₁' d₂') $ restrict s₁' s₂'

-------------------------------------------------------------------------------
-- Properties

data DropLast {X} (d : ℕ) : ∀ {m n} → Vec X m → Vec X n → Set where
  [] : ∀ {xs : Vec X n}
    → n ∸ d ≡ 0
    → DropLast d xs []
  _∷_ : ∀ x {xs : Vec X (d + n)} {ys : Vec X n}
    → DropLast d xs ys
    → DropLast d (x ∷ xs) (x ∷ ys)

pattern []! = [] refl

▻-∷-DropLast : ∀ x (xs : Vec X n) → DropLast 1 (x ∷ xs) (x ▻ xs)
▻-∷-DropLast x [] = []!
▻-∷-DropLast x (x₁ ∷ xs) = x ∷ ▻-∷-DropLast x₁ xs

DropLastᵐ : ℕ → Vec X m → Maybe (Vec X n) → Set
DropLastᵐ d xs = All (DropLast d xs)


mutual

  B∙F : ∀ (e : E d d' X Y) {xs : Vec X n}
    → DropLastᵐ (d + d') xs $ (B⟦ e ⟧_ ∙ F⟦ e ⟧_) xs
  B∙F (map-fold a f g) = B∙F-map-fold a f g
  B∙F (delay x) = B∙F-delay x
  B∙F (hasten x) = B∙F-hasten x
  B∙F (e ⟫ e') = B∙F-⟫ e e'
  B∙F (e ⊗ e') = B∙F-⊗ e e'

  B∙F-map-fold : ∀ a (f : A → X ⇌ Y) g {xs : Vec X n}
    → DropLastᵐ 0 xs $ (B⟦ map-fold a f g ⟧_ ∙ F⟦ map-fold a f g ⟧_) xs
  B∙F-map-fold a f g {[]} = just []!
  B∙F-map-fold a f g {x ∷ xs} with f a .to x in eq
  ... | nothing = nothing
  ... | just y with map-fold-forward (g a x) f g xs in eq₁
  ...   | nothing = nothing
  ...   | just ys rewrite proj₁ (f a .proof x y) eq with map-fold-backward (g a x) f g ys in eq₂
  ...     | nothing = nothing
  ...     | just xs' with B∙F-map-fold (g a x) f g {xs}
  ...       | ih rewrite eq₁ | eq₂ with ih
  ...         | just ih' = just (x ∷ ih')

  B∙F-delay : ∀ {{_ : Eq X}} x {xs : Vec X n}
    → DropLastᵐ 1 xs $ (B⟦ delay x ⟧_ ∙ F⟦ delay x ⟧_) xs
  B∙F-delay x {[]} = just []!
  B∙F-delay x {x₁ ∷ xs} with x == x
  ... | yes refl = just (▻-∷-DropLast x₁ xs)
  ... | no _ = nothing

  B∙F-hasten : ∀ {{_ : Eq X}} x {xs : Vec X n}
    → DropLastᵐ 1 xs $ (B⟦ hasten x ⟧_ ∙ F⟦ hasten x ⟧_) xs
  B∙F-hasten x {[]} = just []!
  B∙F-hasten x {x₁ ∷ xs} with x == x₁
  ... | yes refl = just (▻-∷-DropLast x xs)
  ... | no _ = nothing

  B∙F-⟫ : ∀ {d₁ d₁' d₂ d₂'} (e : E d₁ d₁' X Y) (e' : E d₂ d₂' Y Z) {xs : Vec X n}
    → DropLastᵐ ((d₁ + d₂) + (d₁' + d₂')) xs $ (B⟦ e ⟫ e' ⟧_ ∙ F⟦ e ⟫ e' ⟧_) xs
  B∙F-⟫ e e' {xs} with F⟦ e ⟧ xs | B∙F e {xs}
  ... | nothing | _ = nothing
  ... | just ys | ih₁ with F⟦ e' ⟧ ys | B∙F e' {ys}
  ...   | nothing | _ = nothing
  ...   | just zs | ih₂ = {!   !}

  B∙F-⊗ : ∀ {d₁ d₁' d₂ d₂'} (e : E d₁ d₁' X Y) (e' : E d₂ d₂' Z W) {xzs : Vec (X × Z) n}
    → DropLastᵐ ((d₁ ⊔ d₂) + (d₁' ⊔ d₂')) xzs $ (B⟦ e ⊗ e' ⟧_ ∙ F⟦ e ⊗ e' ⟧_) xzs
  B∙F-⊗ e e' {xzs} with unzip xzs
  ... | xs , zs with F⟦ e ⟧ xs | F⟦ e' ⟧ zs | B∙F e {xs} | B∙F e' {zs}
  ...   | nothing | nothing | _ | _ = nothing
  ...   | nothing | just _ | _ | _ = nothing
  ...   | just _ | nothing | _ | _ = nothing
  ...   | just ys | just ws | ih₁ | ih₂ = {!   !}


  F∙B : ∀ (e : E d d' X Y) {ys : Vec Y n}
    → DropLastᵐ (d + d') ys $ (F⟦ e ⟧_ ∙ B⟦ e ⟧_) ys
  F∙B (map-fold a f g) = F∙B-map-fold a f g
  F∙B (delay x) = F∙B-delay x
  F∙B (hasten x) = F∙B-hasten x
  F∙B (e ⟫ e') = F∙B-⟫ e e'
  F∙B (e ⊗ e') = F∙B-⊗ e e'

  F∙B-map-fold : ∀ a (f : A → X ⇌ Y) g {ys : Vec Y n}
    → DropLastᵐ 0 ys $ (F⟦ map-fold a f g ⟧_ ∙ B⟦ map-fold a f g ⟧_) ys
  F∙B-map-fold a f g {[]} = just []!
  F∙B-map-fold a f g {y ∷ ys} with f a .from y in eq
  ... | nothing = nothing
  ... | just x with map-fold-backward (g a x) f g ys in eq₁
  ...   | nothing = nothing
  ...   | just xs rewrite proj₂ (f a .proof x y) eq with map-fold-forward (g a x) f g xs in eq₂
  ...     | nothing = nothing
  ...     | just ys' with F∙B-map-fold (g a x) f g {ys}
  ...       | ih rewrite eq₁ | eq₂ with ih
  ...         | just ih' = just (y ∷ ih')

  F∙B-delay = B∙F-hasten
  F∙B-hasten = B∙F-delay

  F∙B-⟫ : ∀ {d₁ d₁' d₂ d₂'} (e : E d₁ d₁' X Y) (e' : E d₂ d₂' Y Z) {zs : Vec Z n}
    → DropLastᵐ ((d₁ + d₂) + (d₁' + d₂')) zs $ (F⟦ e ⟫ e' ⟧_ ∙ B⟦ e ⟫ e' ⟧_) zs
  F∙B-⟫ e e' {zs} with B⟦ e' ⟧ zs | F∙B e' {zs}
  ... | nothing | _ = nothing
  ... | just ys | ih₁ with B⟦ e ⟧ ys | F∙B e {ys}
  ...   | nothing | _ = nothing
  ...     | just xs | ih₂ = {!   !}

  F∙B-⊗ : ∀ {d₁ d₁' d₂ d₂'} (e : E d₁ d₁' X Y) (e' : E d₂ d₂' Z W) {yws : Vec (Y × W) n}
    → DropLastᵐ ((d₁ ⊔ d₂) + (d₁' ⊔ d₂')) yws $ (F⟦ e ⊗ e' ⟧_ ∙ B⟦ e ⊗ e' ⟧_) yws
  F∙B-⊗ e e' {yws} with unzip yws
  ... | ys , ws with B⟦ e ⟧ ys | B⟦ e' ⟧ ws | F∙B e {ys} | F∙B e' {ws}
  ...   | nothing | nothing | _ | _ = nothing
  ...   | nothing | just _ | _ | _ = nothing
  ...   | just _ | nothing | _ | _ = nothing
  ...   | just xs | just zs | ih₁ | ih₂ = {!   !}

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
