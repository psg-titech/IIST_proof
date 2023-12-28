module IIST.Syntax where

open import Data.Maybe.Base using ( maybe )
open import Data.Nat.Base using ( ℕ; zero; suc; _+_; _⊔_ )
open import Data.Product.Base using ( _×_; _,_; proj₁; proj₂ )
open import Function using ( _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

open import IIST.Common

private
  variable
    A X Y Z W : Set

-------------------------------------------------------------------------------
-- IIST constructors

infixr 9 _⟫_
infixr 3 _⊗_

data E : Set → Set → Set₁ where
  map-fold : A → (A → X ⇌ Y) → (A → X → A) → E X Y
  delay : {{_ : Eq X}} → X → E X X
  hasten : {{_ : Eq X}} → X → E X X
  _⟫_ : E X Y → E Y Z → E X Z
  _⊗_ : E X Y → E Z W → E (X × Z) (Y × W)

--------------------------------------------------------------------------------

D⟦_⟧ : E X Y → ℕ × ℕ
D⟦ map-fold a f g ⟧ = 0 , 0
D⟦ delay x ⟧ = 0 , 1
D⟦ hasten x ⟧ = 1 , 0
D⟦ e ⟫ e' ⟧ =
  let d₁ , d₁' = D⟦ e ⟧
      d₂ , d₂' = D⟦ e' ⟧
   in d₁ + d₂ , d₂' + d₁'
D⟦ e ⊗ e' ⟧ =
  let d₁ , d₁' = D⟦ e ⟧
      d₂ , d₂' = D⟦ e' ⟧
   in d₁ ⊔ d₂ , d₁' ⊔ d₂'

DF⟦_⟧ DB⟦_⟧ : E X Y → ℕ
DF⟦ e ⟧ = proj₁ D⟦ e ⟧
DB⟦ e ⟧ = proj₂ D⟦ e ⟧

I⟦_⟧ : E X Y → E Y X
I⟦ map-fold a f g ⟧ = map-fold a (inv⇌ ∘ f) (λ a → maybe (g a) a ∘ f a .from)
I⟦ delay x ⟧ = hasten x
I⟦ hasten x ⟧ = delay x
I⟦ e ⟫ e' ⟧ = I⟦ e' ⟧ ⟫ I⟦ e ⟧
I⟦ e ⊗ e' ⟧ = I⟦ e ⟧ ⊗ I⟦ e' ⟧

DF∘I≡DB : ∀ (e : E X Y) → DF⟦ I⟦ e ⟧ ⟧ ≡ DB⟦ e ⟧
DF∘I≡DB (map-fold a f g) = refl
DF∘I≡DB (delay x) = refl
DF∘I≡DB (hasten x) = refl
DF∘I≡DB (e ⟫ e') rewrite DF∘I≡DB e | DF∘I≡DB e' = refl
DF∘I≡DB (e ⊗ e') rewrite DF∘I≡DB e | DF∘I≡DB e' = refl

DB∘I≡DF : ∀ (e : E X Y) → DB⟦ I⟦ e ⟧ ⟧ ≡ DF⟦ e ⟧
DB∘I≡DF (map-fold a f g) = refl
DB∘I≡DF (delay x) = refl
DB∘I≡DF (hasten x) = refl
DB∘I≡DF (e ⟫ e') rewrite DB∘I≡DF e | DB∘I≡DF e' = refl
DB∘I≡DF (e ⊗ e') rewrite DB∘I≡DF e | DB∘I≡DF e' = refl
