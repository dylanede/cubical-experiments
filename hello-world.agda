{-# OPTIONS --cubical --exact-split #-}

module hello-world where

open import IO
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.HITs.HitInt renaming (abs to absℤ ; Sign to Sign'; sign to sign')
open import Cubical.HITs.Rational
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Cubical.Data.Empty

private
  variable
    ℓ ℓ' : Level

const₂ : {A B : Set ℓ} {C : Set ℓ'} → C → A → B → C
const₂ c _ _ = c

record Op< (A B : Set ℓ) (C : A → B → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  infix 5 _<_
  field
    _<_ : (a : A) → (b : B) → C a b
open Op< ⦃ ... ⦄ public

record Op> (A B : Set ℓ) (C : A → B → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  infix 5 _>_
  field
    _>_ : (a : A) → (b : B) → C a b
open Op> ⦃ ... ⦄ public

record Op≥ (A B : Set ℓ) (C : A → B → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  infix 5 _≥_
  field
    _≥_ : (a : A) → (b : B) → C a b
open Op≥ ⦃ ... ⦄ public

record Op≤ (A B : Set ℓ) (C : A → B → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  infix 5 _≤_
  field
    _≤_ : (a : A) → (b : B) → C a b
open Op≤ ⦃ ... ⦄ public

record Op== (A B : Set ℓ) (C : A → B → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  infix 5 _==_
  field
    _==_ : (a : A) → (b : B) → C a b
open Op== ⦃ ... ⦄ public

record Op+ (A B : Set ℓ) (C : A → B → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  infixl 7 _+_
  field
    _+_ : (a : A) → (b : B) → C a b
open Op+ ⦃ ... ⦄ public

record Op- (A B : Set ℓ) (C : A → B → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  infixl 7 _-_
  field
    _-_ : (a : A) → (b : B) → C a b
open Op- ⦃ ... ⦄ public

record Op* (A B : Set ℓ) (C : A → B → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  infixl 8 _*_
  field
    _*_ : (a : A) → (b : B) → C a b
open Op* ⦃ ... ⦄ public

instance
  ℕ< : Op< ℕ ℕ (const₂ Bool)
  _<_ ⦃ ℕ< ⦄ n m = n less-than m where
    _less-than_ : ℕ → ℕ → Bool
    zero less-than zero = false
    zero less-than suc _ = true
    suc _ less-than zero = false
    suc a less-than suc b = a less-than b

instance
 ℕ> : Op> ℕ ℕ (const₂ Bool)
 _>_ ⦃ ℕ> ⦄ n m = n greater-than m where
   _greater-than_ : ℕ → ℕ → Bool
   zero greater-than zero = false
   zero greater-than suc b = false
   suc a greater-than zero = true
   suc a greater-than suc b = a greater-than b

instance
  ℕ≥ : Op≥ ℕ ℕ (const₂ Bool)
  _≥_ ⦃ ℕ≥ ⦄ a b = not (a < b)

instance
  ℕ≤ : Op≤ ℕ ℕ (const₂ Bool)
  _≤_ ⦃ ℕ≤ ⦄ a b = not (a > b)

instance
  ℕ== : Op== ℕ ℕ (const₂ Bool)
  _==_ ⦃ ℕ== ⦄ a b = a eq b where
    _eq_ : ℕ → ℕ → Bool
    zero eq zero = true
    zero eq suc _ = false
    suc _ eq zero = false
    suc a eq suc b = a eq b

a<b≡¬a≥b : {a b : ℕ} → a < b ≡ not (a ≥ b)
a<b≡¬a≥b {a} {b} = sym (notnot (a < b))

a>b≡¬a≤b : {a b : ℕ} → a > b ≡ not (a ≤ b)
a>b≡¬a≤b {a} {b} = sym (notnot (a > b))

instance
  ℕ+ : Op+ ℕ ℕ (const₂ ℕ)
  _+_ ⦃ ℕ+ ⦄ a b = a +ℕ b


instance
  ℕ- : Op- ℕ ℕ (λ a b → ⦃ _ : a ≥ b ≡ true ⦄ → ℕ)
  _-_ ⦃ ℕ- ⦄ a b = a minus b where
    _minus_ : (a : ℕ) → (b : ℕ) → ⦃ _ : a ≥ b ≡ true ⦄ → ℕ
    n minus zero = n
    _minus_ zero (suc b) ⦃ a≥b ⦄ = ⊥-elim (false≢true a≥b)
    (suc a) minus (suc b) = a minus b


instance
  ℕ* : Op* ℕ ℕ (const₂ ℕ)
  _*_ ⦃ ℕ* ⦄ a b = a *ℕ b


--ℤ---------------

instance
  ℤ< : Op< ℤ ℤ (const₂ Bool)
  _<_ ⦃ ℤ< ⦄ n m = n less-than m where
    _less-than_ : ℤ → ℤ → Bool
    pos n less-than pos m = n < m
    neg n less-than neg m = n > m
    pos _ less-than neg _ = false
    neg zero less-than pos zero = false
    neg zero less-than pos (suc _) = true
    neg (suc _) less-than pos _ = true
    pos zero less-than posneg _ = false
    pos (suc _) less-than posneg _ = false
    neg zero less-than posneg _ = false
    neg (suc _) less-than posneg _ = true
    posneg _ less-than pos zero = false
    posneg _ less-than pos (suc _) = true
    posneg _ less-than neg zero = false
    posneg _ less-than neg (suc _) = false
    posneg _ less-than posneg _ = false

instance
  ℤ> : Op> ℤ ℤ (const₂ Bool)
  _>_ ⦃ ℤ> ⦄ n m = n greater-than m where
    _greater-than_ : ℤ → ℤ → Bool
    pos n greater-than pos m = n > m
    neg n greater-than neg m = n < m
    pos zero greater-than neg zero = false
    pos zero greater-than neg (suc _) = true
    pos (suc _) greater-than neg _ = true
    neg _ greater-than pos _ = false
    pos zero greater-than posneg _ = false
    pos (suc _) greater-than posneg _ = true
    neg zero greater-than posneg _ = false
    neg (suc _) greater-than posneg _ = false
    posneg _ greater-than pos zero = false
    posneg _ greater-than pos (suc _) = false
    posneg _ greater-than neg zero = false
    posneg _ greater-than neg (suc _) = true
    posneg _ greater-than posneg _ = false

instance
  ℤ≥ : Op≥ ℤ ℤ (const₂ Bool)
  _≥_ ⦃ ℤ≥ ⦄ a b = not (a < b)

instance
  ℤ≤ : Op≤ ℤ ℤ (const₂ Bool)
  _≤_ ⦃ ℤ≤ ⦄ a b = not (a > b)

instance
  ℤ== : Op== ℤ ℤ (const₂ Bool)
  _==_ ⦃ ℤ== ⦄ a b = a eq b where
    _eq_ : ℤ → ℤ → Bool
    pos n eq pos m = n == m
    neg n eq neg m = n == m
    pos zero eq neg zero = true
    pos zero eq neg (suc _) = false
    pos (suc _) eq neg _ = false
    neg zero eq pos zero = true
    neg zero eq pos (suc _) = false
    neg (suc _) eq pos _ = false
    pos zero eq posneg _ = true
    pos (suc _) eq posneg _ = false
    neg zero eq posneg _ = true
    neg (suc _) eq posneg _ = false
    posneg _ eq pos zero = true
    posneg _ eq pos (suc _) = false
    posneg _ eq neg zero = true
    posneg _ eq neg (suc _) = false
    posneg _ eq posneg _ = true

instance
  ℤ+ : Op+ ℤ ℤ (const₂ ℤ)
  _+_ ⦃ ℤ+ ⦄ a b = a +ℤ b

instance
  ℤ- : Op- ℤ ℤ (const₂ ℤ)
  _-_ ⦃ ℤ- ⦄ a (pos n) = a + (neg n)
  _-_ ⦃ ℤ- ⦄ a (neg n) = a + (pos n)
  _-_ ⦃ ℤ- ⦄ a (posneg _) = a

instance
  ℤ* : Op* ℤ ℤ (const₂ ℤ)
  _*_ ⦃ ℤ* ⦄ a b = a *ℤ b

--ℚ---------------

instance
  ℚ< : Op< ℚ ℚ (const₂ Bool)
  _<_ ⦃ ℚ< ⦄ n m = n less-than m where
    _less-than_ : ℚ → ℚ → Bool
    con u a _ less-than con v b _ = (u * b) < (v * a)
    q@(con u a x) less-than path v b w c y i = {!!} -- Something like `(u * b * c) < ((y i) * a)` ?
    path u a v b x i less-than r = {!!}
    q@(con _ _ _) less-than trunc r r₁ x y i i₁ = BoolIsSet (q less-than r) (q less-than r₁) (cong (q less-than_) x) (cong (q less-than_) y) i i₁
    trunc q q₁ x y i i₁ less-than r = BoolIsSet (q less-than r) (q₁ less-than r) (cong (_less-than r) x) (cong (_less-than r) y) i i₁

private
  -- use of this lemma could be made automatic by changing `path` to take instance arguments instead of implicit arguments.
  -- `nonzero-prod` would then be an instance of `¬ (q * r ≡ pos 0)`
  nonzero-prod : (q r : ℤ) → ¬ (q ≡ pos zero) → ¬ (r ≡ pos zero) → ¬ (q * r ≡ pos 0)
  nonzero-prod (pos (suc n)) (pos (suc m)) _ _ q*r≡0 = snotz (cong absℤ q*r≡0)
  nonzero-prod (pos (suc n)) (neg (suc m)) _ _ q*r≡0 = snotz (cong absℤ q*r≡0)
  nonzero-prod (neg (suc n)) (pos (suc m)) _ _ q*r≡0 = snotz (cong absℤ q*r≡0)
  nonzero-prod (neg (suc n)) (neg (suc m)) _ _ q*r≡0 = snotz (cong absℤ q*r≡0)
  nonzero-prod (pos zero) _ q≢0 _ _ = q≢0 refl
  nonzero-prod (neg zero) _ q≢0 _ _ = q≢0 (sym posneg)
  nonzero-prod (pos (suc _)) (pos zero) _ r≢0 _ = r≢0 refl
  nonzero-prod (pos (suc _)) (neg zero) _ r≢0 _ = r≢0 (sym posneg)
  nonzero-prod (neg (suc _)) (pos zero) _ r≢0 _ = r≢0 refl
  nonzero-prod (neg (suc _)) (neg zero) _ r≢0 _ = r≢0 (sym posneg)
  nonzero-prod q@(pos (suc _)) (posneg i) _ r≢0 _ = r≢0 λ j → posneg (i ∧ ~ j)
  nonzero-prod q@(neg (suc _)) (posneg i) _ r≢0 _ = r≢0 λ j → posneg (i ∧ ~ j)
  nonzero-prod (posneg i) _ q≢0 _ _ = q≢0 λ j → posneg (i ∧ ~ j)

  --+-distrib
  
instance
  ℚ+ : Op+ ℚ ℚ (const₂ ℚ)
  _+_ ⦃ ℚ+ ⦄ q r = q plus r where
    _plus_ : ℚ → ℚ → ℚ
    con u a x plus con v b y = con (u * b + v * a) (a * b) (nonzero-prod a b x y)
    con u a x plus path v b w c {p₁} {p₂} y i = path (u * b + v * a) (a * b) (u * c + w * a) (a * c) {p = nonzero-prod a b x p₁} {q = nonzero-prod a c x p₂} {!!} i
    path u a v b {p₁} {p₂} x i plus con w c y = path (u * c + w * a) (a * c) (v * c + w * b) (b * c) {p = nonzero-prod a c p₁ y} {q = nonzero-prod b c p₂ y} {!!} i
    path u a v b x i plus path u₁ a₁ v₁ b₁ x₁ i₁ = {!!}
    q@(path _ _ _ _ _ _) plus trunc r r₁ x y i i₁ = trunc (q plus r) (q plus r₁) (cong (q plus_) x) (cong (q plus_) y) i i₁
    q@(con _ _ _) plus trunc r r₁ x y i i₁ = trunc (q plus r) (q plus r₁) (cong (q plus_) x) (cong (q plus_) y) i i₁
    trunc q q₁ x y i i₁ plus r = trunc (q plus r) (q₁ plus r) (cong (_plus r) x) (cong (_plus r) y) i i₁
main = run (putStrLn "Hello, World!")

-- infix 10 _~⟨_⟩_

-- data Sign : Set where
--   pos neg zero : Sign

-- data ℤ-has-sign : Sign → ℤ → Set where
--   ℤ-pos : ∀ n → ℤ-has-sign pos (pos (suc n))
--   ℤ-zero : ℤ-has-sign zero (pos zero)
--   ℤ-neg : ∀ n → ℤ-has-sign neg (neg (suc n))

-- ℤ₊ : Set
-- ℤ₊ = Σ ℤ (ℤ-has-sign pos)

-- ℤ₋ : Set
-- ℤ₋ = Σ ℤ (ℤ-has-sign neg)

-- sign-ℤ : (z : ℤ) → Σ[ s ∈ Sign ] (ℤ-has-sign s z)
-- sign-ℤ (pos zero) = zero , ℤ-zero
-- sign-ℤ (pos (suc n)) = pos , ℤ-pos n
-- sign-ℤ (neg zero) = zero , subst (ℤ-has-sign zero) posneg ℤ-zero
-- sign-ℤ (neg (suc n)) = neg , ℤ-neg n
-- sign-ℤ (posneg i) = zero , hfill (λ j → \
--   { (i = i0) → ℤ-zero
--   ; (i = i1) → subst (ℤ-has-sign zero) posneg ℤ-zero
--   }) {!!} i -- no idea

-- data ℚ-has-sign : Sign → ℚ → Set where
--   ℚ-pos₁ : ∀ {u a x} → ℤ-has-sign pos u → ℤ-has-sign pos a → ℚ-has-sign pos (con u a x)
--   ℚ-pos₂ : ∀ {u a x} → ℤ-has-sign neg u → ℤ-has-sign neg a → ℚ-has-sign pos (con u a x)
--   ℚ-zero : ∀ {u a x} → ℤ-has-sign zero u → ℚ-has-sign zero (con u a x)
--   ℚ-neg₁ : ∀ {u a x} → ℤ-has-sign pos u → ℤ-has-sign neg a → ℚ-has-sign neg (con u a x)
--   ℚ-neg₂ : ∀ {u a x} → ℤ-has-sign neg u → ℤ-has-sign pos a → ℚ-has-sign neg (con u a x)

-- ℚ₊ : Set
-- ℚ₊ = Σ ℚ (ℚ-has-sign pos)

-- ℚ₋ : Set
-- ℚ₋ = Σ ℚ (ℚ-has-sign neg)

-- sign-ℚ : (q : ℚ) → Σ[ s ∈ Sign ] (ℚ-has-sign s q)
-- sign-ℚ (con u a x) = case sign-ℤ u , sign-ℤ a of λ
--   { ((pos , u-pos) , pos , a-pos) → pos , ℚ-pos₁ u-pos a-pos
--   ; ((pos , u-pos) , neg , a-neg) → neg , ℚ-neg₁ u-pos a-neg
--   ; ((pos , u-pos) , zero , ℤ-zero) → ⊥-elim (x refl)
--   ; ((neg , u-neg) , pos , a-pos) → neg , ℚ-neg₂ u-neg a-pos
--   ; ((neg , u-neg) , neg , a-neg) → pos , ℚ-pos₂ u-neg a-neg
--   ; ((neg , u-neg) , zero , ℤ-zero) → ⊥-elim (x refl)
--   ; ((zero , u-zero) , _) → zero , ℚ-zero u-zero
--   }
-- sign-ℚ (path u a v b x i) = {!!} -- no idea
-- sign-ℚ (trunc q q₁ x y i i₁) = {!!} -- no idea

-- abs : ℚ → ℚ₊
-- abs q = {!!}

-- {-
-- record Field {n} (F : Set a) : Set a where
--   field
--     +-
--     _+_ : A → A → A
--     _*_ : A → A → A
--     zero : A
--     one : A
-- -}

-- infixl 20 _-_

-- module ⟨ℚ⟩ where
--   _-_ : ℚ → ℚ → ℚ
--   q - r = {!!}
--   _>_ : ℚ → ℚ → Set
--   q > r = ℚ-has-sign pos (q - r)
--   _<_ : ℚ → ℚ → Set
--   q < r = ℚ-has-sign neg (q - r)

-- module ℚ₊ where
--   _>_ : ℚ₊ → ℚ₊ → Set
--   (q , _) > (r , _) = ℚ-has-sign pos (q - r) where open ⟨ℚ⟩
--   _<_ : ℚ₊ → ℚ₊ → Set
--   q < r = r > q
--   _-_ : (q : ℚ₊) → (r : ℚ₊) → ⦃ _ : q > r ⦄ → ℚ₊
--   q - r = {!!}
--   _+_ : ℚ₊ → ℚ₊ → ℚ₊
--   q + r = {!!}

-- data ℝ : Set
-- data _~⟨_⟩_ : ℝ → ℚ₊ → ℝ → Set

-- data ℝ where
--   rat : (q : ℚ) → ℝ
--   lim : (x : ℚ₊ → ℝ) → ((δ ε : ℚ₊) → x δ ~⟨ δ ℚ₊.+ ε ⟩ x ε) → ℝ
--   eq : (u v : ℝ) → ((ε : ℚ₊) → u ~⟨ ε ⟩ v) → u ≡ v

-- data _~⟨_⟩_ where
--   ~-rat-rat : ∀ {q r ε} → abs (q ⟨ℚ⟩.- r) ℚ₊.< ε → rat q ~⟨ ε ⟩ rat r
--   ~-rat-lim : ∀ {q y l δ ε} ⦃ _ : ε ℚ₊.> δ ⦄ → rat q ~⟨ ε ℚ₊.- δ ⟩ y δ → rat q ~⟨ ε ⟩ lim y l
--   ~-lim-rat : ∀ {x l r δ ε} ⦃ _ : ε ℚ₊.> δ ⦄ → x δ ~⟨ ε ℚ₊.- δ ⟩ rat r → lim x l ~⟨ ε ⟩ rat r
--   ~-lim-lim : ∀ {x lₓ y ly ε δ η} ⦃ _ : ε ℚ₊.> δ ⦄ ⦃ _ : (ε ℚ₊.- δ) ℚ₊.> η ⦄ → x δ ~⟨ (ε ℚ₊.- δ) ℚ₊.- η ⟩ y η → lim x lₓ ~⟨ ε ⟩ lim y ly
--   ~-id : ∀ {u v ε} {ζ ξ : u ~⟨ ε ⟩ v} → ζ ≡ ξ
