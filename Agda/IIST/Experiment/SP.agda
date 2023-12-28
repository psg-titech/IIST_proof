{-# OPTIONS --guardedness #-}

module IIST.Experiment.SP where

open import Data.List.Base using ( List; []; _∷_ )
open import Data.Maybe.Base as Maybe using ( Maybe; just; nothing; _>>=_ )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Nat.Instances
open import Data.Nat.Properties using ( ⊔-identityʳ )
open import Data.Product.Base using ( _×_; _,_ )
open import Function using ( case_of_ )
open import Relation.Binary.PropositionalEquality.Core using ( _≡_; refl; sym; cong )
open import Relation.Nullary using ( yes; no )

open import IIST.Common
open import IIST.Syntax

private
  variable
    A X Y Z W : Set

--------------------------------------------------------------------------------
-- A variant of SP

mutual

  data SP (d : ℕ) (X Y : Set) : Set where
    get : ∀ {d'} → d ≡ suc d' → (X → Maybe (∞SP d' X Y)) → SP d X Y
    getput : d ≡ 0 → (X → Maybe (Y × ∞SP 0 X Y)) → SP d X Y

  record ∞SP (d : ℕ) (X Y : Set) : Set where
    coinductive
    field force : SP d X Y

open ∞SP

{-# ETA ∞SP #-}

pattern get! f = get refl f
pattern getput! f = getput refl f

eat : ∀ {d} → SP d X Y → List X → Maybe (List Y)
eat sp [] = just []
eat (get! sp) (x ∷ xs) = do
  sp' ← sp x
  eat (force sp') xs
eat (getput! sp) (x ∷ xs) = do
  y , sp' ← sp x
  Maybe.map (y ∷_) (eat (force sp') xs)

--------------------------------------------------------------------------------
-- Semantics

idSP : SP 0 X X
idSP = getput! λ x → just (x , λ where .force → idSP)

iPre : X → SP 0 X X
iPre x = getput! λ y → just (x , λ where .force → iPre y)

iNext : {{_ : Eq X}} → X → SP 1 X X
iNext x = get! λ y → case x ≟ y of λ
  { (no _) → nothing
  ; (yes _) → just λ where .force → idSP
  }

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → SP 0 X Y
F-map-fold a f g = getput! λ x → case f a .to x of λ
  { nothing → nothing
  ; (just y) → just (y , λ where .force → F-map-fold (g a x) f g)
  }

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → SP 0 Y X
B-map-fold a f g = getput! λ y → case f a .from y of λ
  { nothing → nothing
  ; (just x) → just (x , λ where .force → B-map-fold (g a x) f g)
  }

_∙_ : ∀ {d d'} → SP d X Y → SP d' Y Z → SP (d + d') X Z
get! f ∙ g = get! λ x → case f x of λ
  { nothing → nothing
  ; (just f') → just λ where .force → force f' ∙ g
  }
getput! f ∙ get! g = get! λ x → case f x of λ
  { nothing → nothing
  ; (just (y , f')) → case g y of λ
      { nothing → nothing
      ; (just g') → just λ where .force → force f' ∙ force g'
      }
  }
getput! f ∙ getput! g = getput! λ x → case f x of λ
  { nothing → nothing
  ; (just (y , f')) → case g y of λ
      { nothing → nothing
      ; (just (z , g')) → just (z , λ where .force → force f' ∙ force g')
      }
  }

later : ∀ {d} → SP d X Y → SP (suc d) X Y
later f = get! λ x → just λ where .force → iPre x ∙ f

_∥_ : ∀ {d d'} → SP d X Y → SP d' Z W → SP (d ⊔ d') (X × Z) (Y × W)
get! f ∥ get! g = get! λ (x , z) → case (f x , g z) of λ
  { (just f , just g) → just λ where .force → force f ∥ force g
  ; (_ , _) → nothing
  }
get! f ∥ g@(getput! _) = get (cong suc (sym (⊔-identityʳ _))) λ (x , z) → case f x of λ
  { nothing → nothing
  ; (just f') → just λ where .force → force f' ∥ (iPre z ∙ g)
  }
f@(getput! _) ∥ get! g = get! λ (x , z) → case g z of λ
  { nothing → nothing
  ; (just g') → just λ where .force → (iPre x ∙ f) ∥ force g'
  }
getput! f ∥ getput! g = getput! λ (x , z) → case (f x , g z) of λ
  { (just (y , f') , just (w , g')) →
      just ((y , w) , λ where .force → force f' ∥ force g')
  ; (_ , _) → nothing
  }

--------------------------------------------------------------------------------
-- Example

_ : eat (later idSP) (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (0 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : eat (iPre 100 ∥ iNext 0) ((0 , 0) ∷ (1 , 1) ∷ (2 , 2) ∷ (3 , 3) ∷ [])
  ≡ just ((100 , 1) ∷ (0 , 2) ∷ (1 , 3) ∷ [])
_ = refl
