{-# OPTIONS --guardedness --cubical #-}

module IIST.Semantics.Conversion where

open import Cubical.Foundations.Everything hiding ( id; _∎; step-≡ )
-- open import Data.List.Base as List using ( List; []; _∷_; unzip )
open import Cubical.Data.Maybe.Base using ( Maybe; just; nothing )
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc; _∸_ )
open import Cubical.Data.Sigma using ( _×_; _,_; fst; snd )
open import Cubical.Relation.Nullary.Base using ( yes; no )

open import Codata.PartialColist
open import IIST.Common
open import IIST.Syntax
import IIST.Semantics.Colist as C
-- import IIST.Semantics.List as L
import IIST.Semantics.StateMachine as S

-- open RawMonad {0ℓ} monadMaybe using ( _>=>_; _<$>_; _<*>_; pure )

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

-- --------------------------------------------------------------------------------

-- eat-id : ∀ (xs : List X) → S.eat S.id xs ≡ just xs
-- eat-id [] = refl
-- eat-id (x ∷ xs) rewrite eat-id xs = refl

-- S≡L-shift : ∀ (x : X) xs → S.eat (S.shift x) xs ≡ just (L.shift x xs)
-- S≡L-shift x [] = refl
-- S≡L-shift x (y ∷ xs) rewrite S≡L-shift y xs = refl

-- S≡L-unshift : ∀ {{_ : Eq X}} (x : X) xs → S.eat (S.unshift x) xs ≡ L.unshift x xs
-- S≡L-unshift x [] = refl
-- S≡L-unshift x (y ∷ xs) with x ≟ y
-- ... | no _ = refl
-- ... | yes refl = eat-id xs

-- S≡L-F-map-fold : ∀ a (f : A → X ⇌ Y) g xs → S.eat (S.F-map-fold a f g) xs ≡ L.F-map-fold a f g xs
-- S≡L-F-map-fold a f g [] = refl
-- S≡L-F-map-fold a f g (x ∷ xs) with f a .to x
-- ... | nothing = refl
-- ... | just y rewrite S≡L-F-map-fold (g a x) f g xs = refl

-- >>=-nothing : ∀ (m : Maybe X) → (m >>= λ x → nothing {A = Y}) ≡ nothing
-- >>=-nothing nothing = refl
-- >>=-nothing (just _) = refl

-- >>=-map : ∀ (m : Maybe X) (f : X → Y) (k : Y → Maybe Z)
--   → (Maybe.map f m >>= k) ≡ (m >>= λ x → k (f x))
-- >>=-map (just x) f k = refl
-- >>=-map nothing f k = refl

-- >>=-map′ : ∀ (m : Maybe X) (k : X → Maybe Y) (f : Y → Z)
--   → (m >>= λ x → Maybe.map f (k x)) ≡ Maybe.map f (m >>= k)
-- >>=-map′ (just x) k f = refl
-- >>=-map′ nothing k f = refl

-- <*>-nothingᵣ : ∀ (m : Maybe (X → Y)) → (m <*> nothing) ≡ nothing
-- <*>-nothingᵣ (just _) = refl
-- <*>-nothingᵣ nothing = refl

-- <*>-map₂ : ∀ (f : X → Y) (g : U → V → X) (m : Maybe U) (n : Maybe V)
--   → (f <$> (| g m n |)) ≡ (| (λ u v → f (g u v)) m n |)
-- <*>-map₂ f g (just u) (just v) = refl
-- <*>-map₂ f g (just u) nothing = refl
-- <*>-map₂ f g nothing (just v) = refl
-- <*>-map₂ f g nothing nothing = refl

-- map-<*>₂ : ∀ (f : X → Y → Z) (g : U → X) (h : V → Y) (m : Maybe U) (n : Maybe V)
--   → (| f (g <$> m) (h <$> n) |) ≡ (| (λ x y → f (g x) (h y)) m n |)
-- map-<*>₂ f g h (just u) (just v) = refl
-- map-<*>₂ f g h (just u) nothing = refl
-- map-<*>₂ f g h nothing (just v) = refl
-- map-<*>₂ f g h nothing nothing = refl

-- ⋙-eat-dist : ∀ (f : S.IST X Y d₁) (g : S.IST Y Z d₂) xs
--   → S.eat (f S.⋙ g) xs ≡ (S.eat f >=> S.eat g) xs
-- ⋙′-eatₛ-dist : ∀ (s : S.Step X Y d₁) (g : S.IST Y Z d₂) xs
--   → S.eatₛ (s S.⋙′ g) xs ≡ (S.eatₛ s >=> S.eat g) xs
-- ⋙″-eatₛ-dist : ∀ (f : S.IST X Y 0) (s : S.Step Y Z d) xs
--   → S.eatₛ (f S.⋙″ s) xs ≡ (S.eat f >=> S.eatₛ s) xs
-- ⋙-eat-dist f g [] = refl
-- ⋙-eat-dist f g (x ∷ xs) = ⋙′-eatₛ-dist (S.step f x) g xs
-- ⋙′-eatₛ-dist S.⊥ g xs = refl
-- ⋙′-eatₛ-dist (S.next f) g xs = ⋙-eat-dist f g xs
-- ⋙′-eatₛ-dist (S.yield y f) g xs rewrite >>=-map (S.eat f xs) (y ∷_) (S.eat g) =
--   ⋙″-eatₛ-dist f (S.step g y) xs
-- ⋙″-eatₛ-dist f S.⊥ xs = sym (>>=-nothing (S.eat f xs))
-- ⋙″-eatₛ-dist f (S.next g) xs = ⋙-eat-dist f g xs
-- ⋙″-eatₛ-dist f (S.yield z g) xs rewrite >>=-map′ (S.eat f xs) (S.eat g) (z ∷_) =
--   cong (maybe (λ zs → just (z ∷ zs)) nothing) (⋙-eat-dist f g xs)

-- ⊗′-eat-dist : ∀ (f : S.IST X Y d) (g : S.IST Z W d) xzs
--   → S.eat (f S.⊗′ g) xzs ≡ (S.eat f L.⊗ S.eat g) xzs
-- ⊗ₛ′-eatₛ-dist : ∀ (s : S.Step X Y d) (t : S.Step Z W d) xzs
--   → S.eatₛ (s S.⊗ₛ′ t) xzs ≡ (S.eatₛ s L.⊗ S.eatₛ t) xzs
-- ⊗′-eat-dist f g [] = refl
-- ⊗′-eat-dist f g ((x , z) ∷ xzs) = ⊗ₛ′-eatₛ-dist (S.step f x) (S.step g z) xzs
-- ⊗ₛ′-eatₛ-dist S.⊥ _ xzs = refl
-- ⊗ₛ′-eatₛ-dist (S.next f) S.⊥ xzs = sym (<*>-nothingᵣ (| List.zip (S.eat f (unzip xzs .fst)) |))
-- ⊗ₛ′-eatₛ-dist (S.yield y f) S.⊥ xzs = sym (<*>-nothingᵣ (| List.zip ((y ∷_) <$> S.eat f (unzip xzs .fst)) |))
-- ⊗ₛ′-eatₛ-dist (S.next f) (S.next g) xzs = ⊗′-eat-dist f g xzs
-- ⊗ₛ′-eatₛ-dist (S.yield y f) (S.yield w g) xzs =
--   begin
--     ((y , w) ∷_) <$> S.eat (f S.⊗′ g) xzs
--   ≡⟨ cong (((y , w) ∷_) <$>_) (⊗′-eat-dist f g xzs) ⟩
--     ((y , w) ∷_) <$> (| List.zip (S.eat f (unzip xzs .fst)) (S.eat g (unzip xzs .snd)) |)
--   ≡⟨ <*>-map₂ ((y , w) ∷_) List.zip (S.eat f (unzip xzs .fst)) _ ⟩
--     (| (λ ys ws → (y , w) ∷ List.zip ys ws) (S.eat f (unzip xzs .fst)) (S.eat g (unzip xzs .snd)) |)
--   ≡⟨ sym (map-<*>₂ List.zip (y ∷_) (w ∷_) (S.eat f (unzip xzs .fst)) _) ⟩
--     (| List.zip ((y ∷_) <$> S.eat f (unzip xzs .fst)) ((w ∷_) <$> S.eat g (unzip xzs .snd)) |)
--   ∎
--   where open ≡-Reasoning

-- ⊗-eat-dist : ∀ (f : S.IST X Y d₁) (g : S.IST Z W d₂) xzs
--   → S.eat (f S.⊗ g) xzs ≡ (S.eat f L.⊗ S.eat g) xzs
-- ⊗-eat-dist {d₁ = d₁} {d₂ = d₂} f g xzs =
--   begin
--     S.eat (f S.⊗ g) xzs
--   ≡⟨ ⊗′-eat-dist _ _ xzs ⟩
--     (S.eat (S.cast _ (S.laterN (d₂ ∸ d₁) f)) L.⊗ S.eat (S.cast _ (S.laterN (d₁ ∸ d₂) g))) xzs
--   ≡⟨ {!   !} ⟩
--     (S.eat f L.⊗ S.eat g) xzs
--   ∎
--   where open ≡-Reasoning

-- S≡L-⋙ : {f : S.IST X Y d₁} {f' : L.ST X Y} {g : S.IST Y Z d₂} {g' : L.ST Y Z}
--   → (∀ xs → S.eat f xs ≡ f' xs)
--   → (∀ xs → S.eat g xs ≡ g' xs)
--   → ∀ xs → S.eat (f S.⋙ g) xs ≡ (f' xs >>= g')
-- S≡L-⋙ {f = f} {f'} {g} p q xs rewrite ⋙-eat-dist f g xs | p xs with f' xs
-- ... | nothing = refl
-- ... | just ys = q ys

-- S≡L-⊗ : {f : S.IST X Y d₁} {f' : L.ST X Y} {g : S.IST Z W d₂} {g' : L.ST Z W}
--   → (∀ xs → S.eat f xs ≡ f' xs)
--   → (∀ xs → S.eat g xs ≡ g' xs)
--   → ∀ xs → S.eat (f S.⊗ g) xs ≡ (f' L.⊗ g') xs
-- S≡L-⊗ {f = f} {g = g} p q xzs
--   rewrite ⊗-eat-dist f g xzs | p (unzip xzs .fst) | q (unzip xzs .snd) = refl

-- S≡L-F : ∀ (e : E X Y) xs → S.eat S.F⟦ e ⟧ xs ≡ L.F⟦ e ⟧ xs
-- S≡L-F (`map-fold a f g) = S≡L-F-map-fold a f g
-- S≡L-F (`delay x) = S≡L-shift x
-- S≡L-F (`hasten x) = S≡L-unshift x
-- S≡L-F (e `⋙ e') = S≡L-⋙ (S≡L-F e) (S≡L-F e')
-- S≡L-F (e `⊗ e') = S≡L-⊗ (S≡L-F e) (S≡L-F e')

-- S≡L-B : ∀ (e : E X Y) xs → S.eat S.B⟦ e ⟧ xs ≡ L.B⟦ e ⟧ xs
-- S≡L-B e xs = begin
--   S.eat S.B⟦ e ⟧ xs       ≡⟨ S.≈-eat (S.≈-sym (S.F∘I≈B e)) xs ⟩
--   S.eat S.F⟦ I⟦ e ⟧ ⟧ xs  ≡⟨ S≡L-F I⟦ e ⟧ xs ⟩
--   L.F⟦ I⟦ e ⟧ ⟧ xs        ≡⟨ L.F∘I≡B e xs ⟩
--   L.B⟦ e ⟧ xs             ∎
--   where open ≡-Reasoning

--------------------------------------------------------------------------------

eat∞-id : ∀ (xs : Colist⊥ X) → S.eat∞ S.id xs ≡ xs
eat∞-id [] = refl
eat∞-id ⊥ = refl
eat∞-id (x ∷ xs) i = x ∷ λ where .force → eat∞-id (force xs) i

S≡C-shift : ∀ (x : X) xs → S.eat∞ (S.shift x) xs ≡ C.shift x xs
S≡C-shift x [] = refl
S≡C-shift x ⊥ = refl
S≡C-shift x (y ∷ xs) i = x ∷ λ where .force → S≡C-shift y (force xs) i

S≡C-unshift : ∀ {{_ : Eq X}} (x : X) xs → S.eat∞ (S.unshift x) xs ≡ C.unshift x xs
S≡C-unshift x [] = refl
S≡C-unshift x ⊥ = refl
S≡C-unshift x (y ∷ xs) i with x ≟ y
... | no _ = ⊥
... | yes refl = eat∞-id (force xs) i

S≡C-F-map-fold : ∀ a (f : A → X ⇌ Y) g xs → S.eat∞ (S.F-map-fold a f g) xs ≡ C.F-map-fold a f g xs
S≡C-F-map-fold a f g [] = refl
S≡C-F-map-fold a f g ⊥ = refl
S≡C-F-map-fold a f g (x ∷ xs) i with f a .to x
... | nothing = ⊥
... | just y = y ∷ λ where .force → S≡C-F-map-fold (g a x) f g (force xs) i

⋙-eat∞-dist : ∀ (f : S.IST X Y d₁) (g : S.IST Y Z d₂) xs
  → S.eat∞ (f S.⋙ g) xs ≡ S.eat∞ g (S.eat∞ f xs)
⋙′-eat∞-dist : ∀ (s : S.Step X Y d₁) (g : S.IST Y Z d₂) xs
  → S.eatₛ∞ (s S.⋙′ g) xs ≡ S.eat∞ g (S.eatₛ∞ s xs)
⋙″-eat∞-dist : ∀ (f : S.IST X Y 0) (s : S.Step Y Z d) xs
  → S.eatₛ∞ (f S.⋙″ s) xs ≡ S.eatₛ∞ s (delay (S.eat∞ f (force xs)))
⋙-eat∞-dist f g [] = refl
⋙-eat∞-dist f g ⊥ = refl
⋙-eat∞-dist f g (x ∷ xs) = ⋙′-eat∞-dist (S.step f x) g xs
⋙′-eat∞-dist nothing g xs = refl
⋙′-eat∞-dist {d₁ = zero} (just (y , f)) g xs = ⋙″-eat∞-dist f (S.step g y) xs
⋙′-eat∞-dist {d₁ = suc d₁} (just f) g xs = ⋙-eat∞-dist f g (force xs)
⋙″-eat∞-dist f nothing xs = refl
⋙″-eat∞-dist {d = zero} f (just (z , g)) xs i = z ∷ λ where .force → ⋙-eat∞-dist f g (force xs) i
⋙″-eat∞-dist {d = suc d} f (just g) xs = ⋙-eat∞-dist f g (force xs)

-- ⊗′-eat∞-dist : ∀ (f : S.IST X Y d) (g : S.IST Z W d) xzs
--   → S.eat∞ (f S.⊗′ g) xzs ≈ (S.eat∞ f C.⊗ S.eat∞ g) xzs
-- ⊗ₛ′-eatₛ∞-dist : ∀ (s : S.Step X Y d) (t : S.Step Z W d) xzs
--   → S.eatₛ∞ (s S.⊗ₛ′ t) xzs ≈ zip (S.eatₛ∞ s (delay (unzipₗ (force xzs)))) (S.eatₛ∞ t (delay (unzipᵣ (force xzs))))
-- ⊗′-eat∞-dist f g [] = []
-- ⊗′-eat∞-dist f g ⊥ = ⊥
-- ⊗′-eat∞-dist f g ((x , z) ∷ xzs) = ⊗ₛ′-eatₛ∞-dist (S.step f x) (S.step g z) xzs
-- ⊗ₛ′-eatₛ∞-dist S.⊥ _ xzs = ⊥
-- ⊗ₛ′-eatₛ∞-dist (S.next _) S.⊥ xzs = ≈-sym zip-⊥ᵣ
-- ⊗ₛ′-eatₛ∞-dist (S.yield _ _) S.⊥ xzs = ⊥
-- ⊗ₛ′-eatₛ∞-dist (S.next f) (S.next g) xzs = ⊗′-eat∞-dist f g (force xzs)
-- ⊗ₛ′-eatₛ∞-dist (S.yield y f) (S.yield w g) xzs = (y , w) ∷ λ where .force → ⊗′-eat∞-dist f g (force xzs)

⊗-eat∞-dist : ∀ (f : S.IST X Y d₁) (g : S.IST Z W d₂) xzs
  → S.eat∞ (f S.⊗ g) xzs ≡ (S.eat∞ f C.⊗ S.eat∞ g) xzs
⊗-eat∞-dist f g xzs = {!   !}
-- ⊗-eat∞-dist {d₁ = d₁} {d₂ = d₂} f g xzs =
--   begin
--     S.eat∞ (f S.⊗ g) xzs
--   ≈⟨ ⊗′-eat∞-dist _ _ xzs ⟩
--     (S.eat∞ (S.cast _ (S.laterN (d₂ ∸ d₁) f)) C.⊗ S.eat∞ (S.cast _ (S.laterN (d₁ ∸ d₂) g))) xzs
--   ≈⟨ {!   !} ⟩
--     (S.eat∞ f C.⊗ S.eat∞ g) xzs
--   ∎
--   where open ≈-Reasoning

S≡C-⋙ : {f : S.IST X Y d₁} {f' : C.ST X Y} {g : S.IST Y Z d₂} {g' : C.ST Y Z}
  → (∀ xs → S.eat∞ f xs ≡ f' xs)
  → (∀ xs → S.eat∞ g xs ≡ g' xs)
  → ∀ xs → S.eat∞ (f S.⋙ g) xs ≡ g' (f' xs)
S≡C-⋙ {f = f} {f'} {g} {g'} p q xs =
  S.eat∞ (f S.⋙ g) xs    ≡⟨ ⋙-eat∞-dist f g xs ⟩
  S.eat∞ g (S.eat∞ f xs)  ≡⟨ congS (S.eat∞ g) (p xs) ⟩
  S.eat∞ g (f' xs)        ≡⟨ q (f' xs) ⟩
  g' (f' xs)              ∎
  where open ≡-Reasoning

S≡C-⊗ : {f : S.IST X Y d₁} {f' : C.ST X Y} {g : S.IST Z W d₂} {g' : C.ST Z W}
  → (∀ xs → S.eat∞ f xs ≡ f' xs)
  → (∀ xs → S.eat∞ g xs ≡ g' xs)
  → ∀ xzs → S.eat∞ (f S.⊗ g) xzs ≡ (f' C.⊗ g') xzs
S≡C-⊗ {f = f} {f'} {g} {g'} p q xzs =
  S.eat∞ (f S.⊗ g) xzs         ≡⟨ ⊗-eat∞-dist f g xzs ⟩
  (S.eat∞ f C.⊗ S.eat∞ g) xzs  ≡⟨ cong₂ zip (p (unzipₗ xzs)) (q (unzipᵣ xzs)) ⟩
  (f' C.⊗ g') xzs              ∎
  where open ≡-Reasoning

S≡C-F : ∀ (e : E X Y) xs → S.eat∞ S.F⟦ e ⟧ xs ≡ C.F⟦ e ⟧ xs
S≡C-F (`map-fold a f g) = S≡C-F-map-fold a f g
S≡C-F (`delay x) = S≡C-shift x
S≡C-F (`hasten x) = S≡C-unshift x
S≡C-F (e `⋙ e') = S≡C-⋙ (S≡C-F e) (S≡C-F e')
S≡C-F (e `⊗ e') = S≡C-⊗ (S≡C-F e) (S≡C-F e')

S≡C-B : ∀ (e : E X Y) xs → S.eat∞ S.B⟦ e ⟧ xs ≡ C.B⟦ e ⟧ xs
S≡C-B e xs =
  S.eat∞ S.B⟦ e ⟧ xs       ≡⟨ congP (λ _ f → S.eat∞ f xs) (symP (S.F∘I≡B e)) ⟩
  S.eat∞ S.F⟦ I⟦ e ⟧ ⟧ xs  ≡⟨ S≡C-F I⟦ e ⟧ xs ⟩
  C.F⟦ I⟦ e ⟧ ⟧ xs         ≡⟨ C.F∘I≡B e ≡$ xs ⟩
  C.B⟦ e ⟧ xs              ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------

-- fail : S.IST X Y d
-- S.step fail _ = S.⊥

-- counterexample :
--   S.eat (fail {ℕ} {ℕ} {0} S.⊗ S.later S.id) ((0 , 0) ∷ []) ≢
--   (S.eat (fail {ℕ} {ℕ} {0}) L.⊗ S.eat (S.later S.id)) ((0 , 0) ∷ [])
-- counterexample ()
