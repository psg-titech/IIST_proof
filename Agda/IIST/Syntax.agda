{-# OPTIONS --safe --cubical #-}

module IIST.Syntax where

open import Cubical.Foundations.Everything
open import Cubical.Data.Maybe.Base as Maybe using ()
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Nat.Properties using () renaming ( max to _⊔_ )
open import Cubical.Data.Sigma.Base using ( _×_; _,_; fst; snd )
open import Cubical.Data.Unit.Base using ( tt )

open import IIST.Common

private
  variable
    A X Y Z W : Type

-------------------------------------------------------------------------------
-- IIST constructors

infixr 9 _`⋙_
infixr 3 _`⊗_

data E : Type → Type → Type₁ where
  `map-fold : A → (A → X ⇌ Y) → (A → X → A) → E X Y
  `delay : {{_ : Eq X}} → X → E X X
  `hasten : {{_ : Eq X}} → X → E X X
  _`⋙_ : E X Y → E Y Z → E X Z
  _`⊗_ : E X Y → E Z W → E (X × Z) (Y × W)

`map : X ⇌ Y → E X Y
`map f = `map-fold tt (λ _ → f) (λ _ _ → tt)

--------------------------------------------------------------------------------

D⟦_⟧ : E X Y → ℕ × ℕ
D⟦ `map-fold a f g ⟧ = 0 , 0
D⟦ `delay x ⟧ = 0 , 1
D⟦ `hasten x ⟧ = 1 , 0
D⟦ e `⋙ e' ⟧ =
  let d₁ , d₁' = D⟦ e ⟧
      d₂ , d₂' = D⟦ e' ⟧
   in d₁ + d₂ , d₂' + d₁'
D⟦ e `⊗ e' ⟧ =
  let d₁ , d₁' = D⟦ e ⟧
      d₂ , d₂' = D⟦ e' ⟧
   in d₁ ⊔ d₂ , d₁' ⊔ d₂'

DF⟦_⟧ DB⟦_⟧ : E X Y → ℕ
DF⟦ e ⟧ = fst D⟦ e ⟧
DB⟦ e ⟧ = snd D⟦ e ⟧

I⟦_⟧ : E X Y → E Y X
I⟦ `map-fold a f g ⟧ = `map-fold a (_⇌_.inverse ∘ f) (λ a → Maybe.rec a (g a) ∘ f a .from)
I⟦ `delay x ⟧ = `hasten x
I⟦ `hasten x ⟧ = `delay x
I⟦ e `⋙ e' ⟧ = I⟦ e' ⟧ `⋙ I⟦ e ⟧
I⟦ e `⊗ e' ⟧ = I⟦ e ⟧ `⊗ I⟦ e' ⟧

DF∘I≡DB : ∀ (e : E X Y) → DF⟦ I⟦ e ⟧ ⟧ ≡ DB⟦ e ⟧
DF∘I≡DB (`map-fold a f g) = refl
DF∘I≡DB (`delay x) = refl
DF∘I≡DB (`hasten x) = refl
DF∘I≡DB (e `⋙ e') = cong₂ _+_ (DF∘I≡DB e') (DF∘I≡DB e)
DF∘I≡DB (e `⊗ e') = cong₂ _⊔_ (DF∘I≡DB e) (DF∘I≡DB e')

DB∘I≡DF : ∀ (e : E X Y) → DB⟦ I⟦ e ⟧ ⟧ ≡ DF⟦ e ⟧
DB∘I≡DF (`map-fold a f g) = refl
DB∘I≡DF (`delay x) = refl
DB∘I≡DF (`hasten x) = refl
DB∘I≡DF (e `⋙ e') = cong₂ _+_ (DB∘I≡DF e) (DB∘I≡DF e')
DB∘I≡DF (e `⊗ e') = cong₂ _⊔_ (DB∘I≡DF e) (DB∘I≡DF e')
