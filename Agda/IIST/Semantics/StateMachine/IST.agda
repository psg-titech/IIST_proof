{-# OPTIONS --guardedness --cubical #-}

module IIST.Semantics.StateMachine.IST where

open import Cubical.Foundations.Everything hiding ( step-≡; _∎ )
open import Cubical.Data.Empty as Empty using () renaming ( ⊥ to Empty )
open import Cubical.Data.Maybe.Base as Maybe using ( Maybe; just; nothing )
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc; predℕ; _+_ )
open import Cubical.Data.List.Base using ( List; []; _∷_ )
open import Cubical.Data.Sigma using ( _×_; _,_; fst; snd )
open import Cubical.Data.Unit.Base using ( Unit; tt )

open import IIST.Common
open import IIST.Syntax
open import Codata.PartialColist

private
  variable
    A X Y Z U V W : Type
    d d₁ d₂ d₃ d₄ : ℕ

--------------------------------------------------------------------------------
-- Definitionally d-incremental sequence transformation

record IST (X Y : Type) (d : ℕ) : Type
Step Step′ : (X Y : Type) (d : ℕ) → Type

record IST X Y d where
  coinductive
  field step : X → Step X Y d

Step X Y d = Maybe (Step′ X Y d)

Step′ X Y zero = Y × IST X Y zero
Step′ X Y (suc d) = IST X Y d

open IST public

eat : IST X Y d → List X ⇀ List Y
eatₛ : Step X Y d → List X ⇀ List Y
eat f [] = just []
eat f (x ∷ xs) = eatₛ (step f x) xs
eatₛ nothing xs = nothing
eatₛ {d = zero} (just (y , f)) xs = case eat f xs of λ
  { nothing → nothing
  ; (just ys) → just (y ∷ ys)
  }
eatₛ {d = suc d} (just f) xs = eat f xs

eat∞ : IST X Y d → Colist⊥ X → Colist⊥ Y
eatₛ∞ : Step X Y d → ∞Colist⊥ X → Colist⊥ Y
eat∞ f [] = []
eat∞ f ⊥ = ⊥
eat∞ f (x ∷ xs) = eatₛ∞ (step f x) xs
eatₛ∞ nothing xs = ⊥
eatₛ∞ {d = zero} (just (y , f)) xs = y ∷ λ where .force → eat∞ f (force xs)
eatₛ∞ {d = suc d} (just f) xs = eat∞ f (force xs)

cast : (d₁ ≡ d₂) → IST X Y d₁ → IST X Y d₂
castₛ : (d₁ ≡ d₂) → Step X Y d₁ → Step X Y d₂
cast = subst (IST _ _)
castₛ = subst (Step _ _)

--------------------------------------------------------------------------------
-- Properties

≡-cast : {eq : d₁ ≡ d₂} {f : IST X Y d₁}
  → PathP (λ i → IST X Y (eq (~ i))) (cast eq f) f
≡-cast {eq = eq} {f} = symP (subst-filler (IST _ _) eq f)

≡-castₛ : {eq : d₁ ≡ d₂} {s : Step X Y d₁}
  → PathP (λ i → Step X Y (eq (~ i))) (castₛ eq s) s
≡-castₛ {eq = eq} {s} = symP (subst-filler (Step _ _) eq s)

--------------------------------------------------------------------------------
-- Less defined

infix 4 _⊑_ _⊑ₛ_ _⊑ₛ′_

record _⊑_ (f : IST X Y d₁) (g : IST X Y d₂) : Type
data _⊑ₛ_ (s : Step X Y d₁) (t : Step X Y d₂) : Type
_⊑ₛ′_ : Step X Y d₁ → Step X Y d₂ → Type

record _⊑_ {X Y d₁ d₂} f g where
  coinductive
  field
    same-d : d₁ ≡ d₂
    step : ∀ (x : X) → step f x ⊑ₛ step g x

data _⊑ₛ_ s t where
  con : s ⊑ₛ′ t → s ⊑ₛ t

_⊑ₛ′_ nothing _ = Unit
_⊑ₛ′_ (just _) nothing = Empty
_⊑ₛ′_ {d₁ = zero} {d₂ = suc _} s t = Empty
_⊑ₛ′_ {d₁ = suc _} {d₂ = zero} s t = Empty
_⊑ₛ′_ {d₁ = zero} {d₂ = zero} (just (y , f)) (just (y' , g)) = (y ≡ y') × (f ⊑ g)
_⊑ₛ′_ {d₁ = suc d₁} {d₂ = suc d₂} (just f) (just g) = f ⊑ g

open _⊑_ public

⊑-refl : {f : IST X Y d} → f ⊑ f
⊑ₛ-refl : {s : Step X Y d} → s ⊑ₛ s
same-d ⊑-refl = refl
step (⊑-refl {f = f}) x = ⊑ₛ-refl {s = step f x}
⊑ₛ-refl {s = nothing} = con tt
⊑ₛ-refl {d = zero} {s = just (y , f)} = con (refl , ⊑-refl)
⊑ₛ-refl {d = suc d} {s = just f} = con ⊑-refl

PathP-to-⊑ : {eq : d₁ ≡ d₂} {f : IST X Y d₁} {g : IST X Y d₂}
  → PathP (λ i → IST X Y (eq i)) f g → f ⊑ g
PathP-to-⊑ₛ : {eq : d₁ ≡ d₂} {s : Step X Y d₁} {t : Step X Y d₂}
  → PathP (λ i → Step X Y (eq i)) s t → s ⊑ₛ t
PathP-to-⊑ {eq = eq} {f} = JDep (λ _ _ g _ → f ⊑ g) ⊑-refl eq
PathP-to-⊑ₛ {eq = eq} {s} = JDep (λ _ _ t _ → s ⊑ₛ t) ⊑ₛ-refl eq

≡-to-⊑ : {f g : IST X Y d} → f ≡ g → f ⊑ g
≡-to-⊑ₛ : {s t : Step X Y d} → s ≡ t → s ⊑ₛ t
≡-to-⊑ = PathP-to-⊑
≡-to-⊑ₛ = PathP-to-⊑ₛ

⊑-trans : {f : IST X Y d₁} {g : IST X Y d₂} {h : IST X Y d₃} → f ⊑ g → g ⊑ h → f ⊑ h
⊑ₛ-trans : ∀ {d₁ d₂ d₃} {s : Step X Y d₁} {t : Step X Y d₂} {u : Step X Y d₃} → s ⊑ₛ t → t ⊑ₛ u → s ⊑ₛ u
same-d (⊑-trans f⊑g g⊑h) = same-d f⊑g ∙ same-d g⊑h
step (⊑-trans f⊑g g⊑h) x = ⊑ₛ-trans (step f⊑g x) (step g⊑h x)
⊑ₛ-trans {s = nothing} {t} p q = con tt
⊑ₛ-trans {d₁ = zero} {zero} {zero} {just (u , f)} {just (v , g)} {just (w , h)} (con (p , p')) (con (q , q')) =
  con (p ∙ q , ⊑-trans p' q')
⊑ₛ-trans {d₁ = suc d₁} {suc d₂} {suc d₃} {just f} {just g} {just h} (con p) (con q) =
  con (⊑-trans p q)
⊑ₛ-trans {s = just _} {nothing} (con ()) q
⊑ₛ-trans {t = just _} {nothing} p (con ())
⊑ₛ-trans {d₁ = zero} {suc _} {s = just _} {just _} (con ()) q
⊑ₛ-trans {d₁ = suc _} {zero} {s = just _} {just _} (con ()) q
⊑ₛ-trans {d₂ = zero} {suc _} {t = just _} {just _} p (con ())
⊑ₛ-trans {d₂ = suc _} {zero} {t = just _} {just _} p (con ())

module ⊑-Reasoning where

  infixr 2 step-≡ step-⊑
  infix 3 _∎

  step-≡ : (f : IST X Y d₁) {g : IST X Y d₂} {h : IST X Y d₃}
    → g ⊑ h
    → {eq : d₁ ≡ d₂} → PathP (λ i → IST X Y (eq i)) f g
    → f ⊑ h
  step-≡ f p q = ⊑-trans (PathP-to-⊑ q) p

  syntax step-≡ f p q = f ≡⟨ q ⟩ p

  step-⊑ : (f : IST X Y d₁) {g : IST X Y d₂} {h : IST X Y d₃} → g ⊑ h → f ⊑ g → f ⊑ h
  step-⊑ f p q = ⊑-trans q p

  syntax step-⊑ f p q = f ⊑⟨ q ⟩ p

  _∎ : (f : IST X Y d) → f ⊑ f
  _ ∎ = ⊑-refl

module ⊑ₛ-Reasoning where

  infixr 2 step-≡ step-⊑
  infix 3 _∎

  step-≡ : (f : Step X Y d₁) {g : Step X Y d₂} {h : Step X Y d₃}
    → g ⊑ₛ h
    → {eq : d₁ ≡ d₂} → PathP (λ i → Step X Y (eq i)) f g
    → f ⊑ₛ h
  step-≡ f p q = ⊑ₛ-trans (PathP-to-⊑ₛ q) p

  syntax step-≡ f p q = f ≡⟨ q ⟩ p

  step-⊑ : (f : Step X Y d₁) {g : Step X Y d₂} {h : Step X Y d₃} → g ⊑ₛ h → f ⊑ₛ g → f ⊑ₛ h
  step-⊑ f p q = ⊑ₛ-trans q p

  syntax step-⊑ f p q = f ⊑⟨ q ⟩ p

  _∎ : (f : Step X Y d) → f ⊑ₛ f
  _ ∎ = ⊑ₛ-refl
