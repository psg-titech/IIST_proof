{-# OPTIONS --cubical --guardedness #-}

module IIST.Semantics.StateMachine.Semantics where

open import Cubical.Foundations.Everything hiding ( id; _∎; step-≡ )
open import Cubical.Data.Empty as Empty using () renaming ( ⊥ to Empty )
open import Cubical.Data.Equality using ( pathToEq ) renaming ( _≡_ to _≡′_; refl to refl′ )
open import Cubical.Data.Maybe.Base as Maybe using ( Maybe; just; nothing )
open import Cubical.Data.Maybe.Properties using ( ¬nothing≡just; just-inj )
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc; predℕ; _+_; _∸_ )
open import Cubical.Data.Nat.Properties using ( +-zero; +-suc; +-assoc ) renaming ( max to _⊔_; maxComm to ⊔-comm )
open import Cubical.Data.List.Base using ( List; []; _∷_ )
open import Cubical.Data.Sigma.Base using ( _×_; _,_ )
open import Cubical.Data.Unit.Base using ( Unit; tt )
open import Cubical.Relation.Nullary.Base using ( yes; no )
open import Cubical.Tactics.NatSolver using ( solveℕ! )

open import IIST.Common
open import IIST.Syntax
open import IIST.Semantics.StateMachine.IST

private
  variable
    A X Y Z U V W : Set
    d d₁ d₂ d₃ d₄ : ℕ

--------------------------------------------------------------------------------
-- Misc

module ≡-Reasoning where
  open import Cubical.Foundations.Prelude using ( step-≡; _≡⟨⟩_; _∎ ) public

  infix 1 begin⟨_⟩_

  begin⟨_⟩_ : ∀ (i : I) {x y : A} (p : x ≡ y) → A
  begin⟨ i ⟩ eq = eq i

--------------------------------------------------------------------------------
-- Semantics

infixl 9 _⋙_ _⋙′_ _⋙″_
infixl 8 _⊗_

id : IST X X 0
step id x = just (x , id)

shift : X → IST X X 0
step (shift x) y = just (x , shift y)

unshift : {{_ : Eq X}} → X → IST X X 1
step (unshift x) y = case x ≟ y of λ
  { (no _) → nothing
  ; (yes _) → just id
  }

F-map-fold : A → (A → X ⇌ Y) → (A → X → A) → IST X Y 0
F-map-fold-aux : A → (A → X ⇌ Y) → (A → X → A) → Maybe Y → Step X Y 0
step (F-map-fold a f g) x = F-map-fold-aux (g a x) f g (f a .to x)
F-map-fold-aux a f g nothing = nothing
F-map-fold-aux a f g (just y) = just (y , F-map-fold a f g)

B-map-fold : A → (A → X ⇌ Y) → (A → X → A) → IST Y X 0
B-map-fold-aux : A → (A → X ⇌ Y) → (A → X → A) → Maybe X → Step Y X 0
step (B-map-fold a f g) y = B-map-fold-aux a f g (f a .from y)
B-map-fold-aux a f g nothing = nothing
B-map-fold-aux a f g (just x) = just (x , B-map-fold (g a x) f g)

_⋙_ : IST X Y d₁ → IST Y Z d₂ → IST X Z (d₁ + d₂)
_⋙′_ : Step X Y d₁ → IST Y Z d₂ → Step X Z (d₁ + d₂)
_⋙″_ : IST X Y 0 → Step Y Z d → Step X Z d
step (f ⋙ g) x = step f x ⋙′ g
_⋙′_ nothing g = nothing
_⋙′_ {d₁ = zero} (just (y , f)) g = f ⋙″ step g y
_⋙′_ {d₁ = suc d} (just f) g = just (f ⋙ g)
_⋙″_ f nothing = nothing
_⋙″_ {d = zero} f (just (z , g)) = just (z , f ⋙ g)
_⋙″_ {d = suc d} f (just g) = just (f ⋙ g)

later : IST X Y d → IST X Y (suc d)
step (later f) x = just (shift x ⋙ f)

laterN : ∀ n → IST X Y d → IST X Y (n + d)
laterN zero f = f
laterN (suc n) f = later (laterN n f)

_⊗′_ : IST X Y d → IST Z W d → IST (X × Z) (Y × W) d
_⊗ₛ′_ : Step X Y d → Step Z W d → Step (X × Z) (Y × W) d
step (f ⊗′ g) (x , z) = step f x ⊗ₛ′ step g z
_⊗ₛ′_ nothing t = nothing
_⊗ₛ′_ s nothing = nothing
_⊗ₛ′_ {d = zero} (just (y , f)) (just (w , g)) = just ((y , w) , (f ⊗′ g))
_⊗ₛ′_ {d = suc d} (just f) (just g) = just (f ⊗′ g)

m∸n+n≡m⊔n : ∀ m n → m ∸ n + n ≡ m ⊔ n
m∸n+n≡m⊔n zero zero = refl
m∸n+n≡m⊔n zero (suc n) = refl
m∸n+n≡m⊔n (suc m) zero = congS suc (+-zero m)
m∸n+n≡m⊔n (suc m) (suc n) = +-suc (m ∸ n) n ∙ congS suc (m∸n+n≡m⊔n m n)

_⊗_ : IST X Y d₁ → IST Z W d₂ → IST (X × Z) (Y × W) (d₁ ⊔ d₂)
_⊗_ {d₁ = d₁} {d₂ = d₂} f g =
  cast (m∸n+n≡m⊔n d₂ d₁ ∙ ⊔-comm d₂ d₁) (laterN (d₂ ∸ d₁) f) ⊗′
  cast (m∸n+n≡m⊔n d₁ d₂) (laterN (d₁ ∸ d₂) g)

F⟦_⟧ : (e : E X Y) → IST X Y DF⟦ e ⟧
F⟦ `map-fold a f g ⟧ = F-map-fold a f g
F⟦ `delay x ⟧ = shift x
F⟦ `hasten x ⟧ = unshift x
F⟦ e `⋙ e' ⟧ = F⟦ e ⟧ ⋙ F⟦ e' ⟧
F⟦ e `⊗ e' ⟧ = F⟦ e ⟧ ⊗ F⟦ e' ⟧

B⟦_⟧ : (e : E X Y) → IST Y X DB⟦ e ⟧
B⟦ `map-fold a f g ⟧ = B-map-fold a f g
B⟦ `delay x ⟧ = unshift x
B⟦ `hasten x ⟧ = shift x
B⟦ e `⋙ e' ⟧ = B⟦ e' ⟧ ⋙ B⟦ e ⟧
B⟦ e `⊗ e' ⟧ = B⟦ e ⟧ ⊗ B⟦ e' ⟧

_ : eat id (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : eat (later id) (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (0 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : eat F⟦ `delay 0 ⟧ (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (0 ∷ 0 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : eat F⟦ `hasten 0 ⟧ (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ just (1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : eat F⟦ `hasten 0 ⟧ (100 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ nothing
_ = refl

_ : eat F⟦ `delay 0 `⊗ `hasten 0 ⟧ ((0 , 0) ∷ (1 , 1) ∷ (2 , 2) ∷ (3 , 3) ∷ [])
  ≡ just ((0 , 1) ∷ (0 , 2) ∷ (1 , 3) ∷ [])
_ = refl

--------------------------------------------------------------------------------
-- Properties

⋙-identityₗ : {f : IST X Y d} → id ⋙ f ≡ f
⋙″-identityₗ : {s : Step X Y d} → id ⋙″ s ≡ s
step (⋙-identityₗ {f = f} i) x = ⋙″-identityₗ {s = step f x} i
⋙″-identityₗ {s = nothing} = refl
⋙″-identityₗ {d = zero} {s = just (y , f)} = congS (just ∘ (y ,_)) ⋙-identityₗ
⋙″-identityₗ {d = suc d} {s = just f} = congS just ⋙-identityₗ

⋙-identityᵣ : {f : IST X Y d} → PathP (λ i → IST X Y (+-zero d i)) (f ⋙ id) f
⋙′-identityᵣ : {s : Step X Y d} → PathP (λ i → Step X Y (+-zero d i)) (s ⋙′ id) s
step (⋙-identityᵣ {f = f} i) x = ⋙′-identityᵣ {s = step f x} i
⋙′-identityᵣ {s = nothing} i = nothing
⋙′-identityᵣ {d = zero} {s = just (y , f)} = congP (λ _ → just ∘ (y ,_)) ⋙-identityᵣ
⋙′-identityᵣ {d = suc d} {s = just f} = congP (λ _ → just) ⋙-identityᵣ

⋙-assoc : {f : IST X Y d₁} {g : IST Y Z d₂} {h : IST Z W d₃}
  → PathP (λ i → IST X W (+-assoc d₁ d₂ d₃ i)) (f ⋙ (g ⋙ h)) ((f ⋙ g) ⋙ h)
⋙′-assoc : {s : Step X Y d₁} {g : IST Y Z d₂} {h : IST Z W d₃}
  → PathP (λ i → Step X W (+-assoc d₁ d₂ d₃ i)) (s ⋙′ (g ⋙ h)) ((s ⋙′ g) ⋙′ h)
⋙″-assoc₁ : {f : IST X Y 0} {s : Step Y Z d₂} {h : IST Z W d₃}
  → f ⋙″ (s ⋙′ h) ≡ (f ⋙″ s) ⋙′ h
⋙″-assoc₂ : {f : IST X Y 0} {g : IST Y Z 0} {s : Step Z W d₃}
  → f ⋙″ (g ⋙″ s) ≡ (f ⋙ g) ⋙″ s
step (⋙-assoc {f = f} {g} {h} i) x = ⋙′-assoc {s = step f x} {g} {h} i
⋙′-assoc {s = nothing} i = nothing
⋙′-assoc {d₁ = zero} {s = just (y , f)} {g} = ⋙″-assoc₁ {s = step g y}
⋙′-assoc {d₁ = suc d₁} {s = just f} = congP (λ _ → just) ⋙-assoc
⋙″-assoc₁ {s = nothing} = refl
⋙″-assoc₁ {d₂ = zero} {s = just (z , g)} = ⋙″-assoc₂
⋙″-assoc₁ {d₂ = suc d₂} {s = just g} = congS just ⋙-assoc
⋙″-assoc₂ {s = nothing} = refl
⋙″-assoc₂ {d₃ = zero} {s = just (w , h)} = congS (just ∘ (w ,_)) ⋙-assoc
⋙″-assoc₂ {d₃ = suc d₃} {s = just h} = congS just ⋙-assoc

⋙-later : {f : IST X Y d₁} {g : IST Y Z d₂} → later f ⋙ g ≡ later (f ⋙ g)
step (⋙-later {f = f} {g} i) x = just (⋙-assoc {f = shift x} {g = f} {h = g} (~ i))

⋙-laterN : ∀ n {f : IST X Y d₁} {g : IST Y Z d₂}
  → PathP (λ i → IST X Z (+-assoc n d₁ d₂ (~ i))) (laterN n f ⋙ g) (laterN n (f ⋙ g))
⋙-laterN zero = refl
⋙-laterN (suc n) = ⋙-later ◁ congP (λ _ → later) (⋙-laterN n)

laterN-join : ∀ m n {f : IST X Y d}
  → PathP (λ i → IST X Y (+-assoc m n d i)) (laterN m (laterN n f)) (laterN (m + n) f)
laterN-join zero _ = refl
laterN-join (suc m) n = congP (λ _ → later) (laterN-join m n)

laterN-cast : ∀ {m n} (eq : m ≡ n) {f : IST X Y d}
  → PathP (λ i → IST X Y (eq i + d)) (laterN m f) (laterN n f)
laterN-cast eq {f} = cong (λ m → laterN m f) eq

F∘I≡B : ∀ (e : E X Y) → PathP (λ i → IST Y X (DF∘I≡DB e i)) F⟦ I⟦ e ⟧ ⟧ B⟦ e ⟧
F∘I≡B (`map-fold a f g) = helper a
  where
    helper : ∀ a → F⟦ I⟦ `map-fold a f g ⟧ ⟧ ≡ B⟦ `map-fold a f g ⟧
    step (helper a i) y with f a .from y
    ... | nothing = nothing
    ... | just x = just (x , helper (g a x) i)
F∘I≡B (`delay x) = refl
F∘I≡B (`hasten x) = refl
F∘I≡B (e `⋙ e') = congP₂ (λ _ → _⋙_) (F∘I≡B e') (F∘I≡B e)
F∘I≡B (e `⊗ e') = congP₂ (λ _ → _⊗_) (F∘I≡B e) (F∘I≡B e')

B∘I≡F : ∀ (e : E X Y) → PathP (λ i → IST X Y (DB∘I≡DF e i)) B⟦ I⟦ e ⟧ ⟧ F⟦ e ⟧
B∘I≡F (`map-fold a f g) = helper a
  where
    helper : ∀ a → B⟦ I⟦ `map-fold a f g ⟧ ⟧ ≡ F⟦ `map-fold a f g ⟧
    step (helper a i) x with f a .to x | inspect (f a .to) x
    ... | nothing | [ eq ]ᵢ = nothing
    ... | just y | [ eq ]ᵢ rewrite pathToEq (f a .to→from eq) = just (y , helper (g a x) i)
B∘I≡F (`delay x) = refl
B∘I≡F (`hasten x) = refl
B∘I≡F (e `⋙ e') = congP₂ (λ _ → _⋙_) (B∘I≡F e) (B∘I≡F e')
B∘I≡F (e `⊗ e') = congP₂ (λ _ → _⊗_) (B∘I≡F e) (B∘I≡F e')

--------------------------------------------------------------------------------

_IsIISTOf_ : IST X Y d₁ → IST Y X d₂ → Set
_IsIISTOf_ {d₁ = d₁} {d₂ = d₂} f g = g ⋙ f ⊑ laterN (d₂ + d₁) id

shift-IIST : {{_ : Eq X}} (x : X) → shift x IsIISTOf unshift x
same-d (shift-IIST x) = refl
step (shift-IIST x) x' with x ≟ x'
... | no _ = con tt
... | yes eq = con (≡-to-⊑
  (subst (λ x' → id ⋙ shift x ≡ shift x' ⋙ id) eq (⋙-identityₗ ∙ sym ⋙-identityᵣ)))

unshift-IIST : {{_ : Eq X}} (x : X) → unshift x IsIISTOf shift x
same-d (unshift-IIST x) = refl
step (unshift-IIST x) _ with x ≟ x
... | no contra = Empty.rec (contra refl)
... | yes eq = con ⊑-refl

⊑-cong-⋙ : {f : IST X Y d₁} {f' : IST X Y d₂} {g : IST Y Z d₃} {g' : IST Y Z d₄}
  → f ⊑ f'
  → g ⊑ g'
  → f ⋙ g ⊑ f' ⋙ g'
⊑ₛ-cong-⋙′ : {s : Step X Y d₁} {s' : Step X Y d₂} {g : IST Y Z d₃} {g' : IST Y Z d₄}
  → s ⊑ₛ s'
  → g ⊑ g'
  → s ⋙′ g ⊑ₛ s' ⋙′ g'
⊑ₛ-cong-⋙″ : {f f' : IST X Y 0} {s : Step Y Z d₁} {s' : Step Y Z d₂}
  → f ⊑ f'
  → s ⊑ₛ s'
  → f ⋙″ s ⊑ₛ f' ⋙″ s'
same-d (⊑-cong-⋙ f⊑f' g⊑g') = cong₂ _+_ (same-d f⊑f') (same-d g⊑g')
step (⊑-cong-⋙ f⊑f' g⊑g') x = ⊑ₛ-cong-⋙′ (step f⊑f' x) g⊑g'
⊑ₛ-cong-⋙′ {s = nothing} {s'} (con tt) g⊑g' = con tt
⊑ₛ-cong-⋙′ {s = just _} {nothing} (con ()) g⊑g'
⊑ₛ-cong-⋙′ {d₁ = zero} {zero} {s = just (y , f)} {just (y' , f')} (con (y≡y' , f⊑f')) g⊑g' rewrite pathToEq y≡y' =
  ⊑ₛ-cong-⋙″ f⊑f' (step g⊑g' _)
⊑ₛ-cong-⋙′ {d₁ = zero} {suc d₂} {s = just _} {just _} (con ()) g⊑g'
⊑ₛ-cong-⋙′ {d₁ = suc d₁} {suc d₂} {s = just _} {just _} (con f⊑f') g⊑g' =
  con (⊑-cong-⋙ f⊑f' g⊑g')
⊑ₛ-cong-⋙″ {s = nothing} {s'} f⊑f' p = con tt
⊑ₛ-cong-⋙″ {s = just _} {nothing} f⊑f' (con ())
⊑ₛ-cong-⋙″ {d₁ = zero} {zero} {s = just _} {just _} f⊑f' (con (z≡z' , g⊑g')) =
  con (z≡z' , ⊑-cong-⋙ f⊑f' g⊑g')
⊑ₛ-cong-⋙″ {d₁ = zero} {suc d₂} {s = just _} {just _} f⊑f' (con ())
⊑ₛ-cong-⋙″ {d₁ = suc d₁} {zero} {s = just _} {just _} f⊑f' (con ())
⊑ₛ-cong-⋙″ {d₁ = suc d₁} {suc d₂} {s = just _} {just _} f⊑f' (con g⊑g') =
  con (⊑-cong-⋙ f⊑f' g⊑g')

⊑-cong-later : {f : IST X Y d₁} {g : IST X Y d₂} → f ⊑ g → later f ⊑ later g
same-d (⊑-cong-later f⊑g) = congS suc (same-d f⊑g)
step (⊑-cong-later f⊑g) x = con (⊑-cong-⋙ ⊑-refl f⊑g)

⊑-cong-laterN : ∀ n {f : IST X Y d₁} {g : IST X Y d₂} → f ⊑ g → laterN n f ⊑ laterN n g
⊑-cong-laterN zero f⊑g = f⊑g
⊑-cong-laterN (suc n) f⊑g = ⊑-cong-later (⊑-cong-laterN n f⊑g)

⋙-shift : ∀ {f f' : IST X Y 0} {x y}
  → step f x ≡ just (y , f')
  → f' ⋙ shift y ⊑ shift x ⋙ f
⋙′-shift : ∀ {s : Step X Y 0} {f : IST X Y 0} {x y}
  → step f x ≡ s
  → s ⋙′ shift y ⊑ₛ just (y , shift x ⋙ f)
same-d (⋙-shift eq) = refl
step (⋙-shift eq) x' rewrite pathToEq eq = ⋙′-shift refl
⋙′-shift {s = nothing} eq = con tt
⋙′-shift {s = just _} eq = con (refl , ⋙-shift eq)

later-shift-yield : ∀ {f f' : IST X Y 0} {g : IST Y Z d} {x y}
  → step f x ≡ just (y , f')
  → f' ⋙ (shift y ⋙ g) ⊑ shift x ⋙ (f ⋙ g)
later-shift-yield′ : ∀ {s : Step X Y 0} {f : IST X Y 0} {g : IST Y Z d} {x y}
  → step f x ≡ s
  → s ⋙′ (shift y ⋙ g) ⊑ₛ shift x ⋙″ (f ⋙″ step g y)
same-d (later-shift-yield eq) = refl
step (later-shift-yield eq) x' rewrite pathToEq eq = later-shift-yield′ refl
later-shift-yield′ {s = nothing} eq = con tt
later-shift-yield′ {s = just _} {f = f} {g} eq =
  _ ⋙″ (shift _ ⋙″ step g _)  ≡⟨ ⋙″-assoc₂ ⟩
  (_ ⋙ shift _) ⋙″ step g _   ⊑⟨ ⊑ₛ-cong-⋙″ (⋙-shift {f = f} eq) ⊑ₛ-refl ⟩
  (shift _ ⋙ _) ⋙″ step g _   ≡⟨ sym ⋙″-assoc₂ ⟩
  shift _ ⋙″ (_ ⋙″ step g _)  ∎
  where open ⊑ₛ-Reasoning

later-shift-next : ∀ {f : IST X Y (suc d₁)} {f' : IST X Y d₁} {g : IST Y Z d₂} {x}
  → step f x ≡ just f'
  → f' ⋙ later g ⊑ shift x ⋙ (f ⋙ g)
later-shift-next′ : ∀ {s : Step X Y d₁} {f : IST X Y d₁} {g : IST Y Z d₂} {x}
  → step f x ≡ s
  → s ⋙′ later g ⊑ₛ just (shift x ⋙ (f ⋙ g))
same-d (later-shift-next eq) = +-suc _ _
step (later-shift-next eq) x' rewrite pathToEq eq = later-shift-next′ refl
later-shift-next′ {s = nothing} eq = con tt
later-shift-next′ {d₁ = zero} {s = just _} eq = con (later-shift-yield eq)
later-shift-next′ {d₁ = suc d₁} {s = just _} eq = con (later-shift-next eq)

⊑-⋙-later : {f : IST X Y d₁} {g : IST Y Z d₂} → f ⋙ later g ⊑ later (f ⋙ g)
⊑-⋙́′-later : {f : IST X Y d₁} {g : IST Y Z d₂} {s : Step X Y d₁} {x : X}
  → step f x ≡ s
  → s ⋙′ later g ⊑ₛ just (shift x ⋙ (f ⋙ g))
same-d ⊑-⋙-later = +-suc _ _
step ⊑-⋙-later x = ⊑-⋙́′-later refl
⊑-⋙́′-later {s = nothing} eq = con tt
⊑-⋙́′-later {d₁ = zero} {s = just x} eq = con (later-shift-yield eq)
⊑-⋙́′-later {d₁ = suc d₁} {s = just x} eq = con (later-shift-next eq)

⊑-⋙-laterN : ∀ n {f : IST X Y d₁} {g : IST Y Z d₂} → f ⋙ laterN n g ⊑ laterN n (f ⋙ g)
⊑-⋙-laterN zero = ⊑-refl
⊑-⋙-laterN (suc n) = ⊑-trans ⊑-⋙-later (⊑-cong-later (⊑-⋙-laterN n))

⊑-cong-⊗′ : {f : IST X Y d₁} {f' : IST X Y d₂} {g : IST Z W d₁} {g' : IST Z W d₂}
  → f ⊑ f'
  → g ⊑ g'
  → f ⊗′ g ⊑ f' ⊗′ g'
⊑-cong-⊗ₛ′ : {s : Step X Y d₁} {s' : Step X Y d₂} {t : Step Z W d₁} {t' : Step Z W d₂}
  → s ⊑ₛ s'
  → t ⊑ₛ t'
  → s ⊗ₛ′ t ⊑ₛ s' ⊗ₛ′ t'
same-d (⊑-cong-⊗′ f⊑f' g⊑g') = same-d f⊑f'
step (⊑-cong-⊗′ f⊑f' g⊑g') (x , z) = ⊑-cong-⊗ₛ′ (step f⊑f' x) (step g⊑g' z)
⊑-cong-⊗ₛ′ {s = nothing} p q = con tt
⊑-cong-⊗ₛ′ {s = just _} {t = nothing} p q = con tt
⊑-cong-⊗ₛ′ {d₁ = d₁} {d₂ = d₂} {s = just _} {nothing} (con ()) q
⊑-cong-⊗ₛ′ {d₁ = zero} {d₂ = suc d₂} {s = just _} {just _} (con ()) q
⊑-cong-⊗ₛ′ {d₁ = suc d₁} {d₂ = zero} {s = just _} {just _} (con ()) q
⊑-cong-⊗ₛ′ {d₁ = d₁} {d₂ = d₂} {t = just _} {nothing} p (con ())
⊑-cong-⊗ₛ′ {d₁ = zero} {d₂ = zero} {s = just _} {just _} {just _} {just _} (con (p , p')) (con (q , q')) =
  con (cong₂ _,_ p q , ⊑-cong-⊗′ p' q')
⊑-cong-⊗ₛ′ {d₁ = suc d₁} {d₂ = suc d₂} {s = just _} {just _} {just _} {just _} (con p) (con q) =
  con (⊑-cong-⊗′ p q)

⊑-cong-⊗ : ∀ {d₁ d₂ d₃ d₄} {f : IST X Y d₁} {f' : IST X Y d₂} {g : IST Z W d₃} {g' : IST Z W d₄}
  → f ⊑ f'
  → g ⊑ g'
  → f ⊗ g ⊑ f' ⊗ g'
⊑-cong-⊗ f⊑f' g⊑g' = ⊑-cong-⊗′ (h f⊑f' (same-d g⊑g')) (h g⊑g' (same-d f⊑f'))
  where
    open ⊑-Reasoning

    h : ∀ {m n d₁ d₂ d₃ d₄} {f : IST X Y d₁} {f' : IST X Y d₂}
      → {eq₁ : d₃ ∸ d₁ + d₁ ≡ m} {eq₂ : d₄ ∸ d₂ + d₂ ≡ n}
      → f ⊑ f'
      → d₃ ≡ d₄
      → cast eq₁ (laterN (d₃ ∸ d₁) f) ⊑ cast eq₂ (laterN (d₄ ∸ d₂) f')
    h {d₁ = d₁} {d₂} {d₃} {d₄} {f} {f'} {eq₁} {eq₂} f⊑f' eq =
      cast eq₁ (laterN (d₃ ∸ d₁) f)   ≡⟨ ≡-cast ⟩
      laterN (d₃ ∸ d₁) f              ⊑⟨ ⊑-cong-laterN (d₃ ∸ d₁) f⊑f' ⟩
      laterN (d₃ ∸ d₁) f'             ≡⟨ laterN-cast (cong₂ _∸_ eq (same-d f⊑f')) ⟩
      laterN (d₄ ∸ d₂) f'             ≡⟨ symP ≡-cast ⟩
      cast eq₂ (laterN (d₄ ∸ d₂) f')  ∎

⋙-IIST : ∀ {d₁ d₂ d₃ d₄} {f : IST X Y d₁} {f' : IST Y X d₂} {g : IST Y Z d₃} {g' : IST Z Y d₄}
  → f' IsIISTOf f
  → g' IsIISTOf g
  → (g' ⋙ f') IsIISTOf (f ⋙ g)
⋙-IIST {d₁ = d₁} {d₂} {d₃} {d₄} {f} {f'} {g} {g'} f-inv-f' g-inv-g' =
  (f ⋙ g) ⋙ (g' ⋙ f')                  ≡⟨ symP ⋙-assoc ⟩
  f ⋙ (g ⋙ (g' ⋙ f'))                  ≡⟨ congP (λ _ → f ⋙_) ⋙-assoc ⟩
  f ⋙ ((g ⋙ g') ⋙ f')                  ⊑⟨ ⊑-cong-⋙ ⊑-refl (⊑-cong-⋙ g-inv-g' ⊑-refl) ⟩
  f ⋙ (laterN (d₃ + d₄) id ⋙ f')        ≡⟨ congP (λ _ → f ⋙_) (⋙-laterN (d₃ + d₄)) ⟩
  f ⋙ laterN (d₃ + d₄) (id ⋙ f')        ≡⟨ congS (λ h → f ⋙ laterN (d₃ + d₄) h) ⋙-identityₗ ⟩
  f ⋙ laterN (d₃ + d₄) f'                ⊑⟨ ⊑-⋙-laterN (d₃ + d₄) ⟩
  laterN (d₃ + d₄) (f ⋙ f')              ⊑⟨ ⊑-cong-laterN (d₃ + d₄) f-inv-f' ⟩
  laterN (d₃ + d₄) (laterN (d₁ + d₂) id)  ≡⟨ laterN-join (d₃ + d₄) (d₁ + d₂) ⟩
  laterN ((d₃ + d₄) + (d₁ + d₂)) id       ≡⟨ laterN-cast (h d₃  d₄ d₁ d₂) ⟩
  laterN ((d₁ + d₃) + (d₄ + d₂)) id       ∎
  where
    open ⊑-Reasoning
    open import Cubical.Tactics.NatSolver

    h : ∀ m n o p → (m + n) + (o + p) ≡ (o + m) + (n + p)
    h m n o p = solveℕ!

⊗′-id : Path (IST (X × Y) (X × Y) 0) (id ⊗′ id) id
step (⊗′-id i) xy = just (xy , ⊗′-id i)

⊗ₛ′-⊥ᵣ : ∀ {s : Step X Y d₁} → Path (Step (X × Z) (Y × W) _) (s ⊗ₛ′ nothing) nothing
⊗ₛ′-⊥ᵣ {s = nothing} = refl
⊗ₛ′-⊥ᵣ {d₁ = zero} {s = just _} = refl
⊗ₛ′-⊥ᵣ {d₁ = suc d₁} {s = just _} = refl

⋙-⊗′-interchange : {f : IST X Y d₁} {f' : IST Y Z d₂} {g : IST U V d₁} {g' : IST V W d₂}
  → (f ⊗′ g) ⋙ (f' ⊗′ g') ≡ (f ⋙ f') ⊗′ (g ⋙ g')
⋙′-⊗-interchange : {s : Step X Y d₁} {f' : IST Y Z d₂} {t : Step U V d₁} {g' : IST V W d₂}
  → (s ⊗ₛ′ t) ⋙′ (f' ⊗′ g') ≡ (s ⋙′ f') ⊗ₛ′ (t ⋙′ g')
⋙″-⊗-interchange : {f : IST X Y 0} {s : Step Y Z d₂} {g : IST U V 0} {t : Step V W d₂}
  → (f ⊗′ g) ⋙″ (s ⊗ₛ′ t) ≡ (f ⋙″ s) ⊗ₛ′ (g ⋙″ t)
step (⋙-⊗′-interchange {f = f} {f'} {g} {g'} i) (x , u) =
  ⋙′-⊗-interchange {s = step f x} {f'} {step g u} {g'} i
⋙′-⊗-interchange {s = nothing} {t = _} = refl
⋙′-⊗-interchange {s = just _} {t = nothing} = sym ⊗ₛ′-⊥ᵣ
⋙′-⊗-interchange {d₁ = zero} {s = just (y , f)} {t = just (v , g)} =
  ⋙″-⊗-interchange
⋙′-⊗-interchange {d₁ = suc d₁} {s = just f} {t = just g} =
  congS just ⋙-⊗′-interchange
⋙″-⊗-interchange {s = nothing} {t = _} = refl
⋙″-⊗-interchange {s = just x} {t = nothing} = sym ⊗ₛ′-⊥ᵣ
⋙″-⊗-interchange {d₂ = zero} {s = just (z , f')} {t = just (w , g')} =
  congS (just ∘ ((z , w) ,_)) ⋙-⊗′-interchange
⋙″-⊗-interchange {d₂ = suc d₂} {s = just f'} {t = just g'} =
  congS just ⋙-⊗′-interchange

shift-split : {x : X} {y : Y} → shift (x , y) ≡ shift x ⊗′ shift y
step (shift-split {x = x} {y = y} i) (x' , y') = just ((x , y) , shift-split {x = x'} {y = y'} i)

⊗′-later-dist : {f : IST X Y d} {g : IST Z W d}
  → later (f ⊗′ g) ≡ later f ⊗′ later g
step (⊗′-later-dist {f = f} {g} i) (x , z) = just (begin⟨ i ⟩
  shift (x , z) ⋙ (f ⊗′ g)         ≡⟨ congS (_⋙ (f ⊗′ g)) shift-split ⟩
  (shift x ⊗′ shift z) ⋙ (f ⊗′ g)  ≡⟨ ⋙-⊗′-interchange ⟩
  (shift x ⋙ f) ⊗′ (shift z ⋙ g)  ∎)
  where open ≡-Reasoning

⊗′-laterN-dist : ∀ n {f : IST X Y d} {g : IST Z W d}
  → laterN n (f ⊗′ g) ≡ laterN n f ⊗′ laterN n g
⊗′-laterN-dist zero = refl
⊗′-laterN-dist (suc n) {f} {g} =
  later (laterN n (f ⊗′ g))                 ≡⟨ congS later (⊗′-laterN-dist n) ⟩
  later (laterN n f ⊗′ laterN n g)          ≡⟨ ⊗′-later-dist ⟩
  later (laterN n f) ⊗′ later (laterN n g)  ∎
  where open ≡-Reasoning

⊗′-IIST : {f : IST X Y d₁} {f' : IST Y X d₂} {g : IST Z W d₁} {g' : IST W Z d₂}
  → f' IsIISTOf f
  → g' IsIISTOf g
  → (f' ⊗′ g') IsIISTOf (f ⊗′ g)
⊗′-IIST {d₁ = d₁} {d₂ = d₂} {f = f} {f'} {g} {g'} f-inv-f' g-inv-g' =
  (f ⊗′ g) ⋙ (f' ⊗′ g')                      ≡⟨ ⋙-⊗′-interchange ⟩
  (f ⋙ f') ⊗′ (g ⋙ g')                      ⊑⟨ ⊑-cong-⊗′ f-inv-f' g-inv-g' ⟩
  laterN (d₁ + d₂) id ⊗′ laterN (d₁ + d₂) id  ≡⟨ sym (⊗′-laterN-dist (d₁ + d₂)) ⟩
  laterN (d₁ + d₂) (id ⊗′ id)                 ≡⟨ congS (laterN _) ⊗′-id ⟩
  laterN (d₁ + d₂) id                         ∎
  where open ⊑-Reasoning

⊗-IIST : ∀ {d₁ d₂ d₃ d₄} {f : IST X Y d₁} {f' : IST Y X d₂} {g : IST Z W d₃} {g' : IST W Z d₄}
  → f' IsIISTOf f
  → g' IsIISTOf g
  → (f' ⊗ g') IsIISTOf (f ⊗ g)
⊗-IIST {d₁ = d₁} {d₂} {d₃} {d₄} f-inv-f' g-inv-g' =
  ⊗′-IIST
    (h₂ f-inv-f')
    (⊑-trans (h₂ g-inv-g') (PathP-to-⊑ (laterN-cast (cong₂ _+_ (⊔-comm d₃ d₁) (⊔-comm d₄ d₂)))))
  where
    h : ∀ m n o p → m + n + (o + p) ≡ (m + o) + (n + p)
    h m n o p = solveℕ!

    h₁ : ∀ m n o p → (m ∸ n) + (o ∸ p) + (n + p) ≡ (n ⊔ m) + (p ⊔ o)
    h₁ m n o p =
      (m ∸ n) + (o ∸ p) + (n + p)    ≡⟨ h (m ∸ n) (o ∸ p) _ _ ⟩
      (m ∸ n + n) + (o ∸ p + p)      ≡⟨ cong₂ _+_ (m∸n+n≡m⊔n m n) (m∸n+n≡m⊔n o p) ⟩
      (m ⊔ n) + (o ⊔ p)              ≡⟨ cong₂ _+_ (⊔-comm m n) (⊔-comm o p) ⟩
      (n ⊔ m) + (p ⊔ o)              ∎
      where open ≡-Reasoning

    h₂ : ∀ {m n d₁ d₂ d₃ d₄} {eq₁ : d₃ ∸ d₁ + d₁ ≡ m} {eq₂ : d₄ ∸ d₂ + d₂ ≡ n}
      → {f : IST X Y d₁} {f' : IST Y X d₂}
      → f ⋙ f' ⊑ laterN (d₁ + d₂) id
      → cast eq₁ (laterN (d₃ ∸ d₁) f) ⋙ cast eq₂ (laterN (d₄ ∸ d₂) f')
        ⊑ laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) id
    h₂ {d₁ = d₁} {d₂} {d₃} {d₄} {eq₁} {eq₂} {f} {f'} f-inv-f' =
      cast eq₁ (laterN (d₃ ∸ d₁) f) ⋙ cast eq₂ (laterN (d₄ ∸ d₂) f')  ≡⟨ congP₂ (λ i → _⋙_) ≡-cast ≡-cast ⟩
      laterN (d₃ ∸ d₁) f ⋙ laterN (d₄ ∸ d₂) f'                        ≡⟨ ⋙-laterN (d₃ ∸ d₁) ⟩
      laterN (d₃ ∸ d₁) (f ⋙ laterN (d₄ ∸ d₂) f')                      ⊑⟨ ⊑-cong-laterN (d₃ ∸ d₁) (⊑-⋙-laterN (d₄ ∸ d₂)) ⟩
      laterN (d₃ ∸ d₁) (laterN (d₄ ∸ d₂) (f ⋙ f'))                    ≡⟨ laterN-join (d₃ ∸ d₁) (d₄ ∸ d₂) ⟩
      laterN ((d₃ ∸ d₁) + (d₄ ∸ d₂)) (f ⋙ f')                         ⊑⟨ ⊑-cong-laterN ((d₃ ∸ d₁) + (d₄ ∸ d₂)) f-inv-f' ⟩
      laterN ((d₃ ∸ d₁) + (d₄ ∸ d₂)) (laterN (d₁ + d₂) id)             ≡⟨ laterN-join ((d₃ ∸ d₁) + (d₄ ∸ d₂)) (d₁ + d₂) ⟩
      laterN ((d₃ ∸ d₁) + (d₄ ∸ d₂) + (d₁ + d₂)) id                    ≡⟨ laterN-cast (h₁ d₃ d₁ d₄ d₂) ⟩
      laterN ((d₁ ⊔ d₃) + (d₂ ⊔ d₄)) id                                ∎
      where open ⊑-Reasoning

F-IIST : (e : E X Y) → F⟦ e ⟧ IsIISTOf B⟦ e ⟧
F-IIST (`map-fold a f g) = helper a
  where
    helper : ∀ a → (B⟦ `map-fold a f g ⟧ ⋙ F⟦ `map-fold a f g ⟧) ⊑ id
    same-d (helper a) = refl
    step (helper a) y with f a .from y | inspect (f a .from) y
    ... | nothing | [ eq ]ᵢ = con tt
    ... | just x | [ eq ]ᵢ rewrite pathToEq (f a .from→to eq) = con (refl , helper (g a x))
F-IIST (`delay x) = shift-IIST x
F-IIST (`hasten x) = unshift-IIST x
F-IIST (e `⋙ e') = ⋙-IIST (F-IIST e') (F-IIST e)
F-IIST (e `⊗ e') = ⊗-IIST (F-IIST e) (F-IIST e')

B-IIST : (e : E X Y) → B⟦ e ⟧ IsIISTOf F⟦ e ⟧
B-IIST (`map-fold a f g) = helper a
  where
    helper : ∀ a → (F⟦ `map-fold a f g ⟧ ⋙ B⟦ `map-fold a f g ⟧) ⊑ id
    same-d (helper a) = refl
    step (helper a) x with f a .to x | inspect (f a .to) x
    ... | nothing | [ eq ]ᵢ = con tt
    ... | just y | [ eq ]ᵢ rewrite pathToEq (f a .to→from eq) = con (refl , helper (g a x))
B-IIST (`delay x) = unshift-IIST x
B-IIST (`hasten x) = shift-IIST x
B-IIST (e `⋙ e') = ⋙-IIST (B-IIST e) (B-IIST e')
B-IIST (e `⊗ e') = ⊗-IIST (B-IIST e) (B-IIST e')
