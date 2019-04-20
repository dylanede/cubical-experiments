{-# OPTIONS --cubical --safe --exact-split --without-K #-}

module hello-world where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.HITs.HitInt renaming (abs to absℤ ; Sign to Sign'; sign to sign')
open import Cubical.HITs.Rational
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Agda.Primitive
open import Function

private
  variable
    ℓ ℓ' : Level

const₂ : {A B : Set ℓ} {C : Set ℓ'} → C → A → B → C
const₂ c _ _ = c

record FromNat (A : Set ℓ) : Set (lsuc ℓ) where
  field
    Constraint : ℕ → Set ℓ
    fromNat : (n : ℕ) ⦃ _ : Constraint n ⦄ → A
open FromNat ⦃ ... ⦄ public using (fromNat)

{-# BUILTIN FROMNAT fromNat #-}

record FromNeg (A : Set ℓ) : Set (lsuc ℓ) where
  field
    Constraint : ℕ → Set ℓ
    fromNeg : (n : ℕ) ⦃ _ : Constraint n ⦄ → A
open FromNeg ⦃ ... ⦄ public using (fromNeg)

{-# BUILTIN FROMNEG fromNeg #-}

instance
  NatFromNat : FromNat ℕ
  NatFromNat .FromNat.Constraint _ = Unit
  fromNat ⦃ NatFromNat ⦄ n = n

instance
  ℤFromNat : FromNat ℤ
  ℤFromNat .FromNat.Constraint _ = Unit
  fromNat ⦃ ℤFromNat ⦄ n = pos n

instance
  ℤFromNeg : FromNeg ℤ
  ℤFromNeg .FromNeg.Constraint _ = Unit
  fromNeg ⦃ ℤFromNeg ⦄ n = neg n

instance
  ℚFromNat : FromNat ℚ
  ℚFromNat .FromNat.Constraint _ = Unit
  fromNat ⦃ ℚFromNat ⦄ n = int (pos n)

instance
  ℚFromNeg : FromNeg ℚ
  ℚFromNeg .FromNeg.Constraint _ = Unit
  fromNeg ⦃ ℚFromNeg ⦄ n = int (neg n)

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

record OpUnary- (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  field
    -_ : (a : A) → B a
open OpUnary- ⦃ ... ⦄ public

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
  _>_ ⦃ ℤ> ⦄ n m = m < n

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

instance
  ℤunary- : OpUnary- ℤ (const ℤ)
  -_ ⦃ ℤunary- ⦄ (pos n) = neg n
  -_ ⦃ ℤunary- ⦄ (neg n) = pos n
  -_ ⦃ ℤunary- ⦄ (posneg i) = (sym posneg) i

--ℚ---------------

instance
  ℚ< : Op< ℚ ℚ (const₂ Bool)
  _<_ ⦃ ℚ< ⦄ n m = n less-than m where
    _less-than_ : ℚ → ℚ → Bool
    con u a _ less-than con v b _ = u * b < v * a
    q@(con u a x) less-than path v b w c y i = {!!} -- Something like `u * b * c < (y i) * a` ?
    path u a v b x i less-than r = {!!}
    q@(con _ _ _) less-than trunc r r₁ x y i i₁ = isSetBool (q less-than r) (q less-than r₁) (cong (q less-than_) x) (cong (q less-than_) y) i i₁
    trunc q q₁ x y i i₁ less-than r = isSetBool (q less-than r) (q₁ less-than r) (cong (_less-than r) x) (cong (_less-than r) y) i i₁

instance
  ℚ> : Op> ℚ ℚ (const₂ Bool)
  _>_ ⦃ ℚ> ⦄ n m = m < n

private
  -- use of this lemma could be made automatic by changing `path` to take instance arguments instead of implicit arguments.
  -- `nonzero-prod` would then be an instance of `¬ (q * r ≡ pos 0)`
  nonzero-prod : (q r : ℤ) → ¬ (q ≡ 0) → ¬ (r ≡ 0) → ¬ (q * r ≡ 0)
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
  
  0≡m*ℤ0 : (m : ℤ) → 0 ≡ m * 0
  0≡m*ℤ0 (pos n) = cong pos $ 0≡m*0 n
  0≡m*ℤ0 (neg zero) = refl
  0≡m*ℤ0 (neg (suc n)) = posneg ∙ (cong ℤ.neg $ 0≡m*0 n)
  0≡m*ℤ0 (posneg i) = refl

  0≡0*ℤm : (m : ℤ) → 0 ≡ 0 * m
  0≡0*ℤm (pos n) = refl
  0≡0*ℤm (neg zero) = refl
  0≡0*ℤm (neg (suc n)) = posneg
  0≡0*ℤm (posneg i) = refl

  m≡0+ℤm : (m : ℤ) → m ≡ 0 + m
  m≡0+ℤm (pos zero) = refl
  m≡0+ℤm (neg zero) = sym posneg
  m≡0+ℤm (posneg i) = λ j → posneg (i ∧ ~ j)
  m≡0+ℤm (pos (suc n)) = cong sucℤ $ m≡0+ℤm (pos n)
  m≡0+ℤm (neg (suc n)) = cong predℤ $ m≡0+ℤm (neg n)

  m≡m*1 : (m : ℕ) → m ≡ m * 1
  m≡m*1 zero = refl
  m≡m*1 (suc m) = cong suc $ m≡m*1 m

  m≡m*ℤ1 : (m : ℤ) → m ≡ m * 1
  m≡m*ℤ1 (pos zero) = refl
  m≡m*ℤ1 (pos (suc n)) = cong (ℤ.pos ∘ suc) $ m≡m*1 n
  m≡m*ℤ1 (neg zero) = sym posneg
  m≡m*ℤ1 (neg (suc n)) = cong (ℤ.neg ∘ suc) $ m≡m*1 n
  m≡m*ℤ1 (posneg i) = λ j → posneg (i ∧ ~ j)

  ℤ+-pred : (m n : ℤ) → m + predℤ n ≡ predℤ (m + n)
  ℤ+-pred m (pos zero) = refl
  ℤ+-pred m (pos (suc n)) = sym $ predSucℤ (m + pos n)
  ℤ+-pred m (neg n) = refl
  ℤ+-pred m (posneg i) = refl

  ℤ+-comm-0 : (z : ℤ) → (i : I) → posneg i + z ≡ z
  ℤ+-comm-0 z i = cong (_+ z) (λ j → posneg (i ∧ ~ j)) ∙ sym (m≡0+ℤm z)

  ℤ+-comm-0-0 : (i j : I) → posneg i ≡ posneg j
  ℤ+-comm-0-0 i j = λ k → posneg ((~ k ∧ i) ∨ (k ∧ j))

  ℤ+-comm : (m n : ℤ) → m + n ≡ n + m
  ℤ+-comm (pos zero) (pos zero) = ℤ+-comm-0-0 i0 i0
  ℤ+-comm (neg zero) (neg zero) = ℤ+-comm-0-0 i1 i1
  ℤ+-comm (pos zero) (neg zero) = ℤ+-comm-0-0 i0 i1
  ℤ+-comm (neg zero) (pos zero) = ℤ+-comm-0-0 i1 i0
  ℤ+-comm (posneg i) (pos zero) = ℤ+-comm-0-0 i i0
  ℤ+-comm (posneg i) (neg zero) = ℤ+-comm-0-0 i i1
  ℤ+-comm (pos zero) (posneg j) = ℤ+-comm-0-0 i0 j
  ℤ+-comm (neg zero) (posneg j) = ℤ+-comm-0-0 i1 j
  ℤ+-comm (posneg i) (posneg j) = ℤ+-comm-0-0 i j
  ℤ+-comm (pos zero) (pos (suc n)) = cong sucℤ $ ℤ+-comm-0 (pos n) i0
  ℤ+-comm (neg zero) (pos (suc n)) = cong sucℤ $ ℤ+-comm-0 (pos n) i1
  ℤ+-comm (posneg i) (pos (suc n)) = cong sucℤ $ ℤ+-comm-0 (pos n) i
  ℤ+-comm (pos zero) (neg (suc n)) = cong predℤ $ ℤ+-comm-0 (neg n) i0
  ℤ+-comm (neg zero) (neg (suc n)) = cong predℤ $ ℤ+-comm-0 (neg n) i1
  ℤ+-comm (posneg i) (neg (suc n)) = cong predℤ $ ℤ+-comm-0 (neg n) i
  ℤ+-comm (pos (suc m)) (pos zero) = cong sucℤ $ sym $ ℤ+-comm-0 (pos m) i0
  ℤ+-comm (pos (suc m)) (neg zero) = cong sucℤ $ sym $ ℤ+-comm-0 (pos m) i1
  ℤ+-comm (pos (suc m)) (posneg i) = cong sucℤ $ sym $ ℤ+-comm-0 (pos m) i
  ℤ+-comm (neg (suc m)) (pos zero) = cong predℤ $ sym $ ℤ+-comm-0 (neg m) i0
  ℤ+-comm (neg (suc m)) (neg zero) = cong predℤ $ sym $ ℤ+-comm-0 (neg m) i1
  ℤ+-comm (neg (suc m)) (posneg i) = cong predℤ $ sym $ ℤ+-comm-0 (neg m) i
  ℤ+-comm (pos (suc m)) (pos (suc n)) = cong sucℤ
    ( pos (suc m) + pos n ≡⟨ ℤ+-comm (pos (suc m)) (pos n) ⟩
      pos n + pos (suc m) ≡⟨ refl ⟩
      sucℤ (pos n + pos m) ≡⟨ cong sucℤ $ ℤ+-comm (pos n) (pos m) ⟩
      sucℤ (pos m + pos n) ≡⟨ refl ⟩
      pos m + pos (suc n) ≡⟨ ℤ+-comm (pos m) (pos (suc n)) ⟩
      pos (suc n) + pos m ∎
    )
  ℤ+-comm (neg (suc m)) (pos (suc n)) = 
    ( sucℤ (neg (suc m) + pos n) ≡⟨ cong sucℤ $ ℤ+-comm (neg (suc m)) (pos n) ⟩
      sucℤ (pos n + neg (suc m)) ≡⟨ refl ⟩
      sucℤ (predℤ (pos n + neg m)) ≡⟨ sucPredℤ _ ⟩
      pos n + neg m ≡⟨ ℤ+-comm (pos n) (neg m) ⟩
      neg m + pos n ≡⟨ sym $ predSucℤ _ ⟩
      predℤ (sucℤ (neg m + pos n)) ≡⟨ refl ⟩
      predℤ (neg m + pos (suc n)) ≡⟨ cong predℤ $ ℤ+-comm (neg m) (pos (suc n)) ⟩
      predℤ (pos (suc n) + neg m) ∎
    )
  ℤ+-comm (pos (suc m)) (neg (suc n)) = 
    ( predℤ (pos (suc m) + neg n) ≡⟨ cong predℤ $ ℤ+-comm (pos (suc m)) (neg n) ⟩
      predℤ (neg n + pos (suc m)) ≡⟨ refl ⟩
      predℤ (sucℤ (neg n + pos m)) ≡⟨ predSucℤ _ ⟩
      neg n + pos m ≡⟨ ℤ+-comm (neg n) (pos m) ⟩
      pos m + neg n ≡⟨ sym $ sucPredℤ _ ⟩
      sucℤ (predℤ (pos m + neg n)) ≡⟨ refl ⟩
      sucℤ (pos m + neg (suc n)) ≡⟨ cong sucℤ $ ℤ+-comm (pos m) (neg (suc n)) ⟩
      sucℤ (neg (suc n) + pos m) ∎
    )
  ℤ+-comm (neg (suc m)) (neg (suc n)) = cong predℤ
    ( neg (suc m) + neg n ≡⟨ ℤ+-comm (neg (suc m)) (neg n) ⟩
      neg n + neg (suc m) ≡⟨ refl ⟩
      predℤ (neg n + neg m) ≡⟨ cong predℤ $ ℤ+-comm (neg n) (neg m) ⟩
      predℤ (neg m + neg n) ≡⟨ refl ⟩
      neg m + neg (suc n) ≡⟨ ℤ+-comm (neg m) (neg (suc n)) ⟩
      neg (suc n) + neg m ∎
    )

  lemma : (m n : ℕ) → n + m * suc n ≡ m + n * suc m
  lemma m n =
    ( n + m * suc n ≡⟨ cong (n +_) $ *-suc m n ⟩
      n + (m + m * n) ≡⟨ +-assoc n m (m * n) ⟩
      n + m + m * n ≡⟨ cong (_+ m * n) $ +-comm n m ⟩
      m + n + m * n ≡⟨ cong (m + n +_) $ *-comm m n ⟩
      m + n + n * m ≡⟨ sym $ +-assoc m n (n * m) ⟩
      m + (n + n * m) ≡⟨ cong (m +_) $ sym $ *-suc n m ⟩
      m + n * suc m ∎
    )

  ℤ*-comm : (m n : ℤ) → m * n ≡ n * m
  ℤ*-comm (pos zero) (pos zero) = refl
  ℤ*-comm (neg zero) (pos zero) = refl
  ℤ*-comm (posneg i) (pos zero) = refl
  ℤ*-comm (pos zero) (neg zero) = refl
  ℤ*-comm (neg zero) (neg zero) = refl
  ℤ*-comm (posneg i) (neg zero) = refl
  ℤ*-comm (pos zero) (posneg i) = refl
  ℤ*-comm (neg zero) (posneg i) = refl
  ℤ*-comm (posneg i) (posneg j) = refl
  ℤ*-comm (pos zero) (pos (suc n)) = cong pos $ 0≡m*0 n
  ℤ*-comm (neg zero) (pos (suc n)) = cong pos $ 0≡m*0 n
  ℤ*-comm (posneg i) (pos (suc n)) = cong pos $ 0≡m*0 n
  ℤ*-comm (pos zero) (neg (suc n)) = cong neg $ 0≡m*0 n
  ℤ*-comm (neg zero) (neg (suc n)) = cong neg $ 0≡m*0 n
  ℤ*-comm (posneg i) (neg (suc n)) = cong neg $ 0≡m*0 n
  ℤ*-comm (pos (suc m)) (pos zero) = cong pos $ sym $ 0≡m*0 m
  ℤ*-comm (neg (suc m)) (pos zero) = cong neg $ sym $ 0≡m*0 m
  ℤ*-comm (pos (suc m)) (neg zero) = cong pos $ sym $ 0≡m*0 m
  ℤ*-comm (neg (suc m)) (neg zero) = cong neg $ sym $ 0≡m*0 m
  ℤ*-comm (pos (suc m)) (posneg i) = cong pos $ sym $ 0≡m*0 m
  ℤ*-comm (neg (suc m)) (posneg i) = cong neg $ sym $ 0≡m*0 m
  ℤ*-comm (pos (suc m)) (neg (suc n)) = cong (ℤ.neg ∘ suc) $ lemma m n
  ℤ*-comm (neg (suc m)) (neg (suc n)) = cong (ℤ.pos ∘ suc) $ lemma m n
  ℤ*-comm (pos (suc m)) (pos (suc n)) = cong (ℤ.pos ∘ suc) $ lemma m n
  ℤ*-comm (neg (suc m)) (pos (suc n)) = cong (ℤ.neg ∘ suc) $ lemma m n

  neg-distrib-+ : (m n : ℕ) → neg (m + n) ≡ neg m + neg n
  neg-distrib-+ m zero = cong neg $ +-zero m
  neg-distrib-+ m (suc n) = 
    ( neg (m + suc n) ≡⟨ cong neg $ +-suc m n ⟩
      predℤ (neg (m + n)) ≡⟨ cong predℤ $ neg-distrib-+ m n ⟩
      predℤ (neg m + neg n) ∎
    )

  pos-distrib-+ : (m n : ℕ) → pos (m + n) ≡ pos m + pos n
  pos-distrib-+ m zero = cong pos $ +-zero m
  pos-distrib-+ m (suc n) = 
    ( pos (m + suc n) ≡⟨ cong pos $ +-suc m n ⟩
      sucℤ (pos (m + n)) ≡⟨ cong sucℤ $ pos-distrib-+ m n ⟩
      sucℤ (pos m + pos n) ∎
    )

  lemma2 : (m n : ℕ) → suc (n + m * suc (suc n)) ≡ suc m + (n + m * suc n)
  lemma2 m n = 
    ( suc (n + m * suc (suc n)) ≡⟨ cong (suc ∘ (n +_)) $ *-suc m (suc n) ⟩
      suc (n + (m + m * suc n)) ≡⟨ cong (suc ∘ (n +_)) $ +-comm m (m * suc n) ⟩
      suc (n + (m * suc n + m)) ≡⟨ cong (suc) $ +-assoc n (m * suc n) m ⟩
      suc (n + m * suc n + m) ≡⟨ sym $ +-suc (n + m * suc n) m ⟩
      n + m * suc n + suc m ≡⟨ +-comm (n + m * suc n) (suc m) ⟩
      suc m + (n + m * suc n) ∎
    )

  lemma3 : (m : ℤ) → (i : I) → m * 1 ≡ (m + m * posneg i)
  lemma3 m i = 
    ( m * 1 ≡⟨ sym $ m≡m*ℤ1 m ⟩
      m ≡⟨ refl ⟩
      m + 0 ≡⟨ cong (m +_) $ 0≡m*ℤ0 m ⟩
      m + m * 0 ≡⟨ cong (λ x → m + m * x) (λ j → posneg (i ∧ j)) ⟩
      m + m * posneg i ∎
    )

  ℤ-m+-m≡0 : (m : ℕ) → pos m + neg m ≡ 0
  ℤ-m+-m≡0 zero = refl
  ℤ-m+-m≡0 (suc m) = {!
    ( predℤ (pos (suc m) + neg m) ≡⟨ sym $ ℤ+-pred (neg m) (pos (suc m)) ⟩
      predℤ (pos (suc m)
      0 ∎
    )!}

  ℤ*-suc : (m n : ℤ) → m * sucℤ n ≡ m + m * n
  ℤ*-suc m (pos zero) = lemma3 m i0
  ℤ*-suc m (neg zero) = lemma3 m i1
  ℤ*-suc m (posneg i) = lemma3 m i
  ℤ*-suc (pos zero) (pos (suc n)) = refl
  ℤ*-suc (neg zero) (pos (suc n)) = posneg
  ℤ*-suc (posneg i) (pos (suc n)) = λ j → posneg (i ∧ j)
  ℤ*-suc (pos zero) (neg (suc zero)) = refl
  ℤ*-suc (pos zero) (neg (suc (suc n))) = sym posneg
  ℤ*-suc (neg zero) (neg (suc zero)) = posneg
  ℤ*-suc (neg zero) (neg (suc (suc n))) = refl
  ℤ*-suc (posneg i) (neg (suc zero)) = λ j → posneg (i ∧ j)
  ℤ*-suc (posneg i) (neg (suc (suc n))) =  λ j → posneg (i ∨ ~ j)
  ℤ*-suc (pos (suc m)) (neg (suc zero)) = {!
    ( pos (suc m) * -0 ≡⟨ ⟩
      pos (suc m) * 0 ≡⟨ ⟩
      0 ≡⟨ ⟩
      predℤ (pos (suc m) + neg m) ≡⟨ ⟩
      predℤ (pos (suc m) + neg (m * 1)) ∎
    )!}
  ℤ*-suc (neg (suc m)) (neg (suc zero)) = {!!}
  ℤ*-suc (pos (suc m)) (pos (suc n)) = cong sucℤ
    ( pos (suc (n + m * suc (suc n))) ≡⟨ cong ℤ.pos $ lemma2 m n ⟩
      pos (suc m + (n + m * suc n)) ≡⟨ pos-distrib-+ (suc m) (n + m * suc n) ⟩
      pos (suc m) + pos (n + m * suc n) ∎
    )
  ℤ*-suc (neg (suc m)) (pos (suc n)) = cong predℤ
    ( neg (suc (n + m * suc (suc n))) ≡⟨ cong ℤ.neg $ lemma2 m n ⟩
      neg (suc m + (n + m * suc n)) ≡⟨ neg-distrib-+ (suc m) (n + m * suc n) ⟩
      neg (suc m) + neg (n + m * suc n) ∎
    )
  ℤ*-suc (pos (suc m)) (neg (suc (suc n))) = {!!}
  ℤ*-suc (neg (suc m)) (neg (suc (suc n))) = {!!}

  -- induction on s?
  ℤ*+-right-distrib : (q r s : ℤ) → (q + r) * s ≡ q * s + r * s
  ℤ*+-right-distrib q r (pos zero) = {!!}
  ℤ*+-right-distrib q r (pos (suc n)) = {!!}
  ℤ*+-right-distrib q r (neg zero) = {!!}
  ℤ*+-right-distrib q r (neg (suc n)) = {!!}
  ℤ*+-right-distrib q r (posneg i) = {!!}
  
  --right-distrib : (q r s : ℤ) → (q + r) * s ≡ q * s + r * s
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

private
  neg-assoc* : {a b : ℤ} → - (a * b) ≡ (- a) * b
  neg-assoc* {pos zero} {pos n₁} = sym posneg
  neg-assoc* {pos (suc n)} {pos n₁} = refl
  neg-assoc* {pos zero} {neg zero} = sym posneg
  neg-assoc* {pos zero} {neg (suc n₁)} = posneg
  neg-assoc* {pos (suc n)} {neg zero} = refl
  neg-assoc* {pos (suc n)} {neg (suc n₁)} = refl
  neg-assoc* {pos zero} {posneg i} = sym posneg
  neg-assoc* {pos (suc n)} {posneg i} = refl
  neg-assoc* {neg zero} {pos n₁} = sym posneg
  neg-assoc* {neg (suc n)} {pos n₁} = refl
  neg-assoc* {neg zero} {neg zero} = sym posneg
  neg-assoc* {neg (suc n)} {neg zero} = refl
  neg-assoc* {neg zero} {neg (suc n₁)} = posneg
  neg-assoc* {neg (suc n)} {neg (suc n₁)} = refl
  neg-assoc* {neg zero} {posneg i} = sym posneg
  neg-assoc* {neg (suc n)} {posneg i} = refl
  neg-assoc* {posneg i} {pos n} = sym posneg
  neg-assoc* {posneg i} {neg zero} = sym posneg
  neg-assoc* {posneg i} {neg (suc n)} = posneg
  neg-assoc* {posneg i} {posneg i₁} = sym posneg

instance
  ℚunary- : OpUnary- ℚ (const ℚ)
  -_ ⦃ ℚunary- ⦄ q = negative q where
    negative : ℚ → ℚ
    negative (con u a x) = con (- u) a x
    negative (path u a v b {p} {q} x i) = path (- u) a (- v) b {p = p} {q = q}
      ((sym $ neg-assoc* {a = u} {b = b}) ∙ cong -_ x ∙ neg-assoc* {a = v} {b = a})
      i
    negative (trunc q q₁ x y i i₁) = trunc (negative q) (negative q₁) (cong negative x) (cong negative y) i i₁

instance
  ℚ- : Op- ℚ ℚ (const₂ ℚ)
  _-_ ⦃ ℚ- ⦄ q r = q + (- r)

private
  pabsℤ : ℤ → ℤ
  pabsℤ = pos ∘ absℤ

  abs-distrib* : {a b : ℤ} → pabsℤ (a * b) ≡ pabsℤ a * pabsℤ b
  abs-distrib* {pos n} {pos n₁} = refl
  abs-distrib* {pos n} {neg zero} = refl
  abs-distrib* {pos n} {neg (suc n₁)} = refl
  abs-distrib* {pos n} {posneg i} = refl
  abs-distrib* {neg zero} {pos n₁} = refl
  abs-distrib* {neg (suc n)} {pos n₁} = refl
  abs-distrib* {neg zero} {neg zero} = refl
  abs-distrib* {neg zero} {neg (suc n₁)} = refl
  abs-distrib* {neg (suc n)} {neg zero} = refl
  abs-distrib* {neg (suc n)} {neg (suc n₁)} = refl
  abs-distrib* {neg zero} {posneg i} = refl
  abs-distrib* {neg (suc n)} {posneg i} = refl
  abs-distrib* {posneg i} {pos n} = refl
  abs-distrib* {posneg i} {neg zero} = refl
  abs-distrib* {posneg i} {neg (suc n)} = refl
  abs-distrib* {posneg i} {posneg i₁} = refl

  abs-zero : {a : ℤ} → pabsℤ a ≡ 0 → a ≡ 0
  abs-zero {pos zero} _ = refl
  abs-zero {pos (suc _)} p = p
  abs-zero {neg zero} _ = sym posneg
  abs-zero {neg (suc _)} p = cong (neg ∘ absℤ) p ∙ (sym posneg)
  abs-zero {posneg i} _ = λ j → posneg (i ∧ ~ j)

abs : ℚ → ℚ
abs (con u a x) = con (pabsℤ u) (pabsℤ a) λ y → x (abs-zero y) 
abs (path u a v b {p} {q} x i) = path (pabsℤ u) (pabsℤ a) (pabsℤ v) (pabsℤ b)
  {p = λ x → p (abs-zero x)}
  {q = λ x → q (abs-zero x)}
  ((sym $ abs-distrib* {a = u} {b = b}) ∙ cong pabsℤ x ∙ abs-distrib* {a = v} {b = a})
  i
abs (trunc q q₁ x y i i₁) = trunc (abs q) (abs q₁) (cong abs x) (cong abs y) i i₁

infix 10 _~⟨_⟩_

data ℝ : Set
data _~⟨_⟩_ : ℝ → (tol : ℚ) → ⦃ _ : tol > 0 ≡ true ⦄ → ℝ → Set

data ℝ where
  rat : (q : ℚ) → ℝ
  lim : (x : ℚ → ℝ) → ((δ ε : ℚ) ⦃ _ : δ + ε > 0 ≡ true ⦄ → x δ ~⟨ δ + ε ⟩ x ε) → ℝ
  eq : (u v : ℝ) → ((ε : ℚ) ⦃ _ : ε > 0 ≡ true ⦄ → u ~⟨ ε ⟩ v) → u ≡ v

data _~⟨_⟩_ where
  ~-rat-rat : ∀ {q r ε} ⦃ _ : ε > 0 ≡ true ⦄ → abs (q - r) < ε ≡ true → rat q ~⟨ ε ⟩ rat r
  ~-rat-lim : ∀ {q y l δ ε} ⦃ _ : ε - δ > 0 ≡ true ⦄ ⦃ _ : ε > 0 ≡ true ⦄ → rat q ~⟨ ε - δ ⟩ y δ → rat q ~⟨ ε ⟩ lim y l
  ~-lim-rat : ∀ {x l r δ ε} ⦃ _ : ε - δ > 0 ≡ true ⦄ ⦃ _ : ε > 0 ≡ true ⦄ → x δ ~⟨ ε - δ ⟩ rat r → lim x l ~⟨ ε ⟩ rat r
  ~-lim-lim : ∀ {x lₓ y ly ε δ η} ⦃ _ : ε > 0 ≡ true ⦄ ⦃ _ : ε - δ - η > 0 ≡ true ⦄ → x δ ~⟨ ε - δ - η ⟩ y η → lim x lₓ ~⟨ ε ⟩ lim y ly
  ~-isProp : ∀ {u v ε} ⦃ _ : ε > 0 ≡ true ⦄ → isProp (u ~⟨ ε ⟩ v)

