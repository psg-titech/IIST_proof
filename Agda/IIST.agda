module IIST where

open import Category.Monad using ( RawMonad )
open RawMonad {{...}} using ( _>>=_; return ) renaming ( _<=<_ to _∙_ )
open import Data.List using ( List; []; _∷_ )
import Data.List.Properties
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Maybe.Categorical using ( monad )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Maybe.Relation.Unary.All using ( All; just; nothing )
open import Data.Nat using ( ℕ; zero; suc; _⊔_; _⊓_; _+_; _∸_; pred )
open import Data.Nat.Properties using ( +-assoc; +-comm ; ∸-+-assoc ; ∸-distribˡ-⊓-⊔ ; ∸-distribˡ-⊔-⊓; +-suc; +-identityʳ; 0∸n≡0; [m+n]∸[m+o]≡n∸o; m+n∸m≡n )
open import Data.Product using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
import Data.Product.Properties
open import Data.Unit using ( ⊤; tt )
import Data.Unit.Properties
open import Data.Vec using ( Vec; []; _∷_; unzip; restrict )
open import Function using ( _$_ )
open import Relation.Nullary using ( Dec; yes; no )
open import Relation.Binary.PropositionalEquality

infix 0 _⇀_ _⇌_ _↔_ _$?_
infixr 9 _⟫_
infixr 3 _⊗_
infixr 5 _∷!_

instance
  maybeMonad = monad

private
  variable
    m n o p d d' : ℕ
    A X Y Z W : Set

-------------------------------------------------------------------------------
-- Misc.

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (Q → P)

shift : X → Vec X n → Vec X n
shift _ [] = []
shift x (y ∷ xs) = x ∷ shift y xs

_ : shift 0 (1 ∷ 2 ∷ 3 ∷ []) ≡ 0 ∷ 1 ∷ 2 ∷ []
_ = refl

_$?_ = All

m≡n+o→m∸n≡o : ∀ {m n o}
  → m ≡ n + o
  → m ∸ n ≡ o
m≡n+o→m∸n≡o {n = n} {o = o} p rewrite p | m+n∸m≡n n o = refl

m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 : ∀ {m n o p}
  → m ∸ n ≡ 0
  → o ∸ p ≡ 0
  → m ⊓ o ∸ (n ⊔ p) ≡ 0
m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {zero} {zero} {zero} {zero} eq₁ eq₂ = refl
m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {zero} {zero} {zero} {suc p} eq₁ eq₂ = refl
m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {zero} {zero} {suc o} {suc p} eq₁ eq₂ = refl
m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {zero} {suc n} {zero} {zero} eq₁ eq₂ = refl
m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {zero} {suc n} {zero} {suc p} eq₁ eq₂ = refl
m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {zero} {suc n} {suc o} {suc p} eq₁ eq₂ = refl
m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {suc m} {suc n} {zero} {zero} eq₁ eq₂ = refl
m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {suc m} {suc n} {zero} {suc p} eq₁ eq₂ = refl
m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {suc m} {suc n} {suc o} {suc p} eq₁ eq₂ = m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {m} {n} {o} {p} eq₁ eq₂

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

⇌-id : X ⇌ X
⇌-id .to = just
⇌-id .from = just
⇌-id .invertible _ _ = sym , sym

boom : X ⇌ X
boom .to _ = nothing
boom .from _ = nothing
boom .invertible _ _ = (λ ()) , (λ ())

-------------------------------------------------------------------------------
-- Eq typeclass

record Eq (A : Set) : Set where
  infix 4 _==_
  field
    _==_ : (x y : A) → Dec (x ≡ y)

open Eq {{...}}

instance

  eqUnit : Eq ⊤
  _==_ {{eqUnit}} = Data.Unit.Properties._≟_

  eqNat : Eq ℕ
  _==_ {{eqNat}} = Data.Nat.Properties._≟_

  eqProd : {{_ : Eq X}} {{_ : Eq Y}} → Eq (X × Y)
  _==_ {{eqProd}} = Data.Product.Properties.≡-dec _==_ _==_

  eqList : {{_ : Eq X}} → Eq (List X)
  _==_ {{eqList}} = Data.List.Properties.≡-dec _==_

-------------------------------------------------------------------------------
-- Syntax

data E : ℕ → ℕ → Set → Set → Set₁ where
  map-fold : A → (A → X ⇌ Y) → (A → X → A) → E 0 0 X Y
  delay : {{_ : Eq X}} → X → E 0 1 X X
  hasten : {{_ : Eq X}} → X → E 1 0 X X
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
  delay-forward x s = return $ shift x s

  hasten-forward : {{_ : Eq X}} → X → Vec X n ⇀ Vec X (n ∸ 1)
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
    return $ subst (Vec _) (⟫-forward-cast n d₁ d₂) s₂

  ⟫-forward-cast : ∀ n d₁ d₂ → n ∸ d₁ ∸ d₂ ≡ n ∸ (d₁ + d₂)
  ⟫-forward-cast = ∸-+-assoc

  ⊗-forward : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Z W
    → Vec (X × Z) n ⇀ Vec (Y × W) (n ∸ (d₁ ⊔ d₂))
  ⊗-forward {n = n} {d₁ = d₁} {d₂ = d₂} e e' s with s₁ , s₂ ← unzip s = do
    s₁' ← F⟦ e ⟧ s₁
    s₂' ← F⟦ e' ⟧ s₂
    return $ subst (Vec _) (⊗-forward-cast n d₁ d₂) $ restrict s₁' s₂'

  ⊗-forward-cast : ∀ n d₁ d₂ → (n ∸ d₁) ⊓ (n ∸ d₂) ≡ n ∸ (d₁ ⊔ d₂)
  ⊗-forward-cast n d₁ d₂ = sym $ ∸-distribˡ-⊔-⊓ n d₁ d₂

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
    return $ subst (Vec _) (⟫-backward-cast n d₁' d₂') s₂

  ⟫-backward-cast : ∀ n d₁' d₂' → n ∸ d₂' ∸ d₁' ≡ n ∸ (d₁' + d₂')
  ⟫-backward-cast n d₁' d₂' = trans (∸-+-assoc n d₂' d₁') (cong (n ∸_) (+-comm d₂' d₁'))

  ⊗-backward : ∀ {d₁ d₁' d₂ d₂'}
    → E d₁ d₁' X Y
    → E d₂ d₂' Z W
    → Vec (Y × W) n ⇀ Vec (X × Z) (n ∸ (d₁' ⊔ d₂'))
  ⊗-backward {n = n} {d₁' = d₁'} {d₂' = d₂'} e e' s with s₁ , s₂ ← unzip s = do
    s₁' ← B⟦ e ⟧ s₁
    s₂' ← B⟦ e' ⟧ s₂
    return $ subst (Vec _) (⊗-backward-cast n d₁' d₂') $ restrict s₁' s₂'

  ⊗-backward-cast = ⊗-forward-cast

-------------------------------------------------------------------------------
-- DropLast

data DropLast {X} (d : ℕ) : ∀ {m n} → Vec X m → Vec X n → Set where
  [] : ∀ {xs : Vec X n}
    → n ∸ d ≡ 0
    → DropLast d xs []
  cons : ∀ {xs : Vec X m} {ys : Vec X n}
    → m ≡ d + n
    → (x : X)
    → DropLast d xs ys
    → DropLast d (x ∷ xs) (x ∷ ys)

pattern []! = [] refl
pattern _∷!_ x dl = cons refl x dl

_ : DropLast 0 (0 ∷ 1 ∷ 2 ∷ []) (0 ∷ 1 ∷ 2 ∷ [])
_ = 0 ∷! 1 ∷! 2 ∷! []!

_ : DropLast 2 (0 ∷ 1 ∷ 2 ∷ []) (0 ∷ [])
_ = 0 ∷! []!

_ : DropLast 5 (0 ∷ 1 ∷ 2 ∷ []) []
_ = []!

DropLast-reflexive : ∀ (xs : Vec X n) → DropLast 0 xs xs
DropLast-reflexive [] = []!
DropLast-reflexive (x ∷ xs) = x ∷! DropLast-reflexive xs

≡-to-DropLast : ∀ {xs ys : Vec X n} → xs ≡ ys → DropLast 0 xs ys
≡-to-DropLast {xs = xs} refl = DropLast-reflexive xs

DropLast-to-≡ : ∀ {xs ys : Vec X n} → DropLast 0 xs ys → xs ≡ ys
DropLast-to-≡ {xs = []} ([] _) = refl
DropLast-to-≡ (cons p x dl) = cong (x ∷_) (DropLast-to-≡ dl)

DropLast-trans : ∀ {xs : Vec X m} {ys : Vec X n} {zs : Vec X o}
  → DropLast d xs ys
  → DropLast d' ys zs
  → DropLast (d + d') xs zs
DropLast-trans {m = m} {d = d} {d' = d'} ([] p) ([] q)
  with m ∸ (d + d') in eq | sym (∸-+-assoc m d d')
... | .(m ∸ d ∸ d') | refl rewrite p | q = [] eq
DropLast-trans {d = d} {d' = d'} (cons {m = m} {n = n} p _ _) ([] q)
  rewrite sym ([m+n]∸[m+o]≡n∸o d (suc n) d') | +-suc d n | sym p = [] q
DropLast-trans {d = d} {d' = d'} (cons {m = m} p x dl) (cons {n = n} q _ dl')
  rewrite p | q | sym (+-assoc d d' n) = x ∷! DropLast-trans dl dl'

Droplast-∷-shift : ∀ x (xs : Vec X n) → DropLast 1 (x ∷ xs) (shift x xs)
Droplast-∷-shift x [] = []!
Droplast-∷-shift x (y ∷ xs) = x ∷! Droplast-∷-shift y xs

DropLast-shift-shift : ∀ {xs : Vec X m} {ys : Vec X n}
  → DropLast d xs ys
  → ∀ x → DropLast d (shift x xs) (shift x ys)
DropLast-shift-shift ([] p) x = [] p
DropLast-shift-shift (cons p y dl) x = cons p x (DropLast-shift-shift dl y)

DropLast-unzip : ∀ {xys : Vec (X × Y) m} {xys' : Vec (X × Y) n} {xs ys xs' ys'}
  → DropLast d xys xys'
  → unzip xys ≡ (xs , ys)
  → unzip xys' ≡ (xs' , ys')
  → DropLast d xs xs' × DropLast d ys ys'
DropLast-unzip ([] p) refl refl = [] p , [] p
DropLast-unzip (cons {xs = xys} {ys = xys'} p (x , y) dl) refl refl
    with unzip xys in eq | unzip xys' in eq'
... | xs , ys | xs' , ys' with DropLast-unzip dl eq eq'
...   | dl₁ , dl₂ = cons p x dl₁ , cons p y dl₂

DropLast-restrict : ∀ {xs : Vec X m} {xs' : Vec X n} {ys : Vec X o} {ys' : Vec X p}
  → DropLast d xs xs'
  → DropLast d' ys ys'
  → DropLast (d ⊔ d') (restrict xs ys) (restrict xs' ys')
DropLast-restrict {d = d} ([] {n = n} p) ([] q) = [] (m∸n≡0→o∸p≡0→[m⊓o]∸[n⊔p]≡0 {n} {d} p q)
DropLast-restrict ([] p) (cons q y dl') = [] {!   !}
DropLast-restrict (cons p x dl) ([] q) = [] {!   !}
DropLast-restrict (cons p x dl) (cons q y dl') = cons {!   !} (x , y) (DropLast-restrict dl dl')

-------------------------------------------------------------------------------
-- Properties

-- F-DropLast : ∀ (e : E d d' X Y) {xs : Vec X m} {xs' : Vec X n} {ys : Vec Y (m ∸ d)}
--   → DropLast o xs xs'
--   → F⟦ e ⟧ xs ≡ just ys
--   → Σ[ ys' ∈ Vec Y (n ∸ d) ] F⟦ e ⟧ xs' ≡ just ys' × DropLast o ys ys'
-- F-DropLast (map-fold a f g) ([] p)  _ = [] , refl , [] p
-- F-DropLast (map-fold a f g) (cons {xs = xs} {ys = xs'} refl x dl) p with f a .to x | p
-- ... | just y | p' with map-fold-forward (g a x) f g xs in eq | p'
-- ...   | just ys | p'' with F-DropLast (map-fold (g a x) f g) dl eq
-- ...     | ys' , q , dl' rewrite sym (just-injective p'') | q = y ∷ ys' , refl , y ∷! dl'
-- F-DropLast (delay x) {xs' = xs'} dl p rewrite sym $ just-injective p
--   = shift x xs' , refl , DropLast-shift-shift dl x
-- F-DropLast (hasten x) ([] p) _ = [] , refl , [] {!   !}
-- F-DropLast (hasten x) (cons {ys = xs'} p x' dl) q with x == x' | q
-- ... | yes refl | refl = xs' , refl , dl
-- F-DropLast (e ⟫ e') {xs} dl p with F⟦ e ⟧ xs in eq | p
-- ... | just ys | p' with F-DropLast e dl eq
-- ...   | ys' , q , dl' with F⟦ e' ⟧ ys in eq' | p'
-- ...     | just zs | p'' with F-DropLast e' dl' eq'
-- ...       | ih = {!   !}
-- F-DropLast (e ⊗ e') dl p = {!   !}

mutual

  B∙F⟦_⟧_ : E d d' X Y → Vec X n ⇀ Vec X (n ∸ d ∸ d')
  B∙F⟦_⟧_ e = B⟦ e ⟧_ ∙ F⟦ e ⟧_

  B∙F : ∀ (e : E d d' X Y) {xs : Vec X n}
    → DropLast (d + d') xs $? B∙F⟦ e ⟧ xs
  B∙F (map-fold a f g) = B∙F-map-fold a f g
  B∙F (delay x) = B∙F-delay x
  B∙F (hasten x) = B∙F-hasten x
  B∙F (e ⟫ e') = B∙F-⟫ e e'
  B∙F (e ⊗ e') = B∙F-⊗ e e'

  B∙F-map-fold : ∀ a (f : A → X ⇌ Y) g {xs : Vec X n}
    → DropLast 0 xs $? B∙F⟦ map-fold a f g ⟧ xs
  B∙F-map-fold a f g {[]} = just []!
  B∙F-map-fold a f g {x ∷ xs} with f a .to x in eq
  ... | nothing = nothing
  ... | just y with map-fold-forward (g a x) f g xs in eq₁
  ...   | nothing = nothing
  ...   | just ys rewrite f a .invertible x y .proj₁ eq with map-fold-backward (g a x) f g ys in eq₂
  ...     | nothing = nothing
  ...     | just xs' with B∙F-map-fold (g a x) f g {xs}
  ...       | ih rewrite eq₁ | eq₂ with ih
  ...         | just ih' = just (x ∷! ih')

  B∙F-delay : ∀ {{_ : Eq X}} x {xs : Vec X n}
    → DropLast 1 xs $? B∙F⟦ delay x ⟧ xs
  B∙F-delay x {[]} = just []!
  B∙F-delay x {y ∷ xs} with x == x
  ... | yes refl = just (Droplast-∷-shift y xs)
  ... | no _ = nothing

  B∙F-hasten : ∀ {{_ : Eq X}} x {xs : Vec X n}
    → DropLast 1 xs $? B∙F⟦ hasten x ⟧ xs
  B∙F-hasten x {[]} = just []!
  B∙F-hasten x {y ∷ xs} with x == y
  ... | yes refl = just (Droplast-∷-shift x xs)
  ... | no _ = nothing

  B∙F-⟫ : ∀ {d₁ d₁' d₂ d₂'} (e : E d₁ d₁' X Y) (e' : E d₂ d₂' Y Z) {xs : Vec X n}
    → DropLast ((d₁ + d₂) + (d₁' + d₂')) xs $? B∙F⟦ e ⟫ e' ⟧ xs
  B∙F-⟫ {n = n} {d₁ = d₁} {d₁' = d₁'} {d₂ = d₂} {d₂' = d₂'} e e' {xs} with F⟦ e ⟧ xs | B∙F e {xs}
  ... | nothing | _ = nothing
  ... | just ys | ih₁ with F⟦ e' ⟧ ys | B∙F e' {ys}
  ...   | nothing | _ = nothing
  ...   | just zs | ih₂ rewrite ⟫-forward-cast n d₁ d₂ with B⟦ e' ⟧ zs | ih₂
  ...     | nothing | _ = nothing
  ...     | just ys' | just ih₂' with B⟦ e ⟧ ys' | ih₁
  ...       | nothing | _ = nothing
  ...       | just xs' | ih₁' rewrite ⟫-backward-cast (n ∸ (d₁ + d₂)) d₁' d₂' = {!   !}

  B∙F-⊗ : ∀ {d₁ d₁' d₂ d₂'} (e : E d₁ d₁' X Y) (e' : E d₂ d₂' Z W) {xzs : Vec (X × Z) n}
    → DropLast ((d₁ ⊔ d₂) + (d₁' ⊔ d₂')) xzs $? B∙F⟦ e ⊗ e' ⟧ xzs
  B∙F-⊗ {n = n} {d₁ = d₁} {d₁' = d₁'} {d₂ = d₂} {d₂' = d₂'} e e' {xzs} with unzip xzs
  ... | xs , zs with F⟦ e ⟧ xs | F⟦ e' ⟧ zs | B∙F e {xs} | B∙F e' {zs}
  ...   | nothing | nothing | _ | _ = nothing
  ...   | nothing | just _ | _ | _ = nothing
  ...   | just _ | nothing | _ | _ = nothing
  ...   | just ys | just ws | ih₁ | ih₂ with restrict ys ws
  ...     | yws rewrite ⊗-forward-cast n d₁ d₂ with unzip yws
  ...       | ys' , ws' with B⟦ e ⟧ ys' | B⟦ e' ⟧ ws'
  ...         | nothing | nothing = nothing
  ...         | just _ | nothing = nothing
  ...         | nothing | just _ = nothing
  ...         | just xs' | just zs' with restrict xs' zs'
  ...           | xzs' rewrite ⊗-backward-cast (n ∸ (d₁ ⊔ d₂)) d₁' d₂' = {!   !}


  F∙B⟦_⟧_ : E d d' X Y → Vec Y n ⇀ Vec Y (n ∸ d' ∸ d)
  F∙B⟦_⟧_ e = F⟦ e ⟧_ ∙ B⟦ e ⟧_

  F∙B : ∀ (e : E d d' X Y) {ys : Vec Y n}
    → DropLast (d + d') ys $? F∙B⟦ e ⟧ ys
  F∙B (map-fold a f g) = F∙B-map-fold a f g
  F∙B (delay x) = F∙B-delay x
  F∙B (hasten x) = F∙B-hasten x
  F∙B (e ⟫ e') = F∙B-⟫ e e'
  F∙B (e ⊗ e') = F∙B-⊗ e e'

  F∙B-map-fold : ∀ a (f : A → X ⇌ Y) g {ys : Vec Y n}
    → DropLast 0 ys $? F∙B⟦ map-fold a f g ⟧ ys
  F∙B-map-fold a f g {[]} = just []!
  F∙B-map-fold a f g {y ∷ ys} with f a .from y in eq
  ... | nothing = nothing
  ... | just x with map-fold-backward (g a x) f g ys in eq₁
  ...   | nothing = nothing
  ...   | just xs rewrite f a .invertible x y .proj₂ eq with map-fold-forward (g a x) f g xs in eq₂
  ...     | nothing = nothing
  ...     | just ys' with F∙B-map-fold (g a x) f g {ys}
  ...       | ih rewrite eq₁ | eq₂ with ih
  ...         | just ih' = just (y ∷! ih')

  F∙B-delay = B∙F-hasten
  F∙B-hasten = B∙F-delay

  F∙B-⟫ : ∀ {d₁ d₁' d₂ d₂'} (e : E d₁ d₁' X Y) (e' : E d₂ d₂' Y Z) {zs : Vec Z n}
    → DropLast ((d₁ + d₂) + (d₁' + d₂')) zs $? F∙B⟦ e ⟫ e' ⟧ zs
  F∙B-⟫ e e' {zs} with B⟦ e' ⟧ zs | F∙B e' {zs}
  ... | nothing | _ = nothing
  ... | just ys | ih₁ with B⟦ e ⟧ ys | F∙B e {ys}
  ...   | nothing | _ = nothing
  ...     | just xs | ih₂ = {!   !}

  F∙B-⊗ : ∀ {d₁ d₁' d₂ d₂'} (e : E d₁ d₁' X Y) (e' : E d₂ d₂' Z W) {yws : Vec (Y × W) n}
    → DropLast ((d₁ ⊔ d₂) + (d₁' ⊔ d₂')) yws $? F∙B⟦ e ⊗ e' ⟧ yws
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
