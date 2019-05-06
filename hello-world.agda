{-# OPTIONS --cubical --safe --exact-split --without-K #-}

module hello-world where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Relation.Nullary
open import Cubical.HITs.HitInt renaming (abs to absℤ ; Sign to Sign'; sign to sign')
open import Cubical.HITs.Rational
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Prod
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

-- use of this lemma could be made automatic by changing `path` in ℚ to take instance arguments instead of implicit arguments.
-- `nonzero-prod` would then be an instance of `¬ (q * r ≡ pos 0)`
-- however currently, since `¬ (q * r ≡ pos 0)` is a function type, it is not allowed as an instance argument type
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

ℤ+-suc : (m n : ℤ) → m + sucℤ n ≡ sucℤ (m + n)
ℤ+-suc m (pos zero) = refl
ℤ+-suc m (pos (suc n)) = refl
ℤ+-suc m (neg zero) = refl
ℤ+-suc m (neg (suc n)) = sym $ sucPredℤ (m + neg n)
ℤ+-suc m (posneg i) = refl

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
  ( pos (suc m) + pos n  ≡⟨ ℤ+-comm (pos (suc m)) (pos n) ⟩
    pos n + pos (suc m)  ≡⟨ refl ⟩
    sucℤ (pos n + pos m) ≡⟨ cong sucℤ $ ℤ+-comm (pos n) (pos m) ⟩
    sucℤ (pos m + pos n) ≡⟨ refl ⟩
    pos m + pos (suc n)  ≡⟨ ℤ+-comm (pos m) (pos (suc n)) ⟩
    pos (suc n) + pos m  ∎
  )
ℤ+-comm (neg (suc m)) (pos (suc n)) = 
  ( sucℤ (neg (suc m) + pos n)   ≡⟨ cong sucℤ $ ℤ+-comm (neg (suc m)) (pos n) ⟩
    sucℤ (pos n + neg (suc m))   ≡⟨ refl ⟩
    sucℤ (predℤ (pos n + neg m)) ≡⟨ sucPredℤ _ ⟩
    pos n + neg m                ≡⟨ ℤ+-comm (pos n) (neg m) ⟩
    neg m + pos n                ≡⟨ sym $ predSucℤ _ ⟩
    predℤ (sucℤ (neg m + pos n)) ≡⟨ refl ⟩
    predℤ (neg m + pos (suc n))  ≡⟨ cong predℤ $ ℤ+-comm (neg m) (pos (suc n)) ⟩
    predℤ (pos (suc n) + neg m)  ∎
  )
ℤ+-comm (pos (suc m)) (neg (suc n)) = 
  ( predℤ (pos (suc m) + neg n)  ≡⟨ cong predℤ $ ℤ+-comm (pos (suc m)) (neg n) ⟩
    predℤ (neg n + pos (suc m))  ≡⟨ refl ⟩
    predℤ (sucℤ (neg n + pos m)) ≡⟨ predSucℤ _ ⟩
    neg n + pos m                ≡⟨ ℤ+-comm (neg n) (pos m) ⟩
    pos m + neg n                ≡⟨ sym $ sucPredℤ _ ⟩
    sucℤ (predℤ (pos m + neg n)) ≡⟨ refl ⟩
    sucℤ (pos m + neg (suc n))   ≡⟨ cong sucℤ $ ℤ+-comm (pos m) (neg (suc n)) ⟩
    sucℤ (neg (suc n) + pos m)   ∎
  )
ℤ+-comm (neg (suc m)) (neg (suc n)) = cong predℤ
  ( neg (suc m) + neg n   ≡⟨ ℤ+-comm (neg (suc m)) (neg n) ⟩
    neg n + neg (suc m)   ≡⟨ refl ⟩
    predℤ (neg n + neg m) ≡⟨ cong predℤ $ ℤ+-comm (neg n) (neg m) ⟩
    predℤ (neg m + neg n) ≡⟨ refl ⟩
    neg m + neg (suc n)   ≡⟨ ℤ+-comm (neg m) (neg (suc n)) ⟩
    neg (suc n) + neg m   ∎
  )

ℤ+-assoc : (m n o : ℤ) → m + (n + o) ≡ m + n + o
ℤ+-assoc m n (pos zero) = refl
ℤ+-assoc m n (pos (suc o)) = 
  ( m + sucℤ (n + pos o)   ≡⟨ ℤ+-suc m (n + pos o) ⟩
    sucℤ (m + (n + pos o)) ≡⟨ cong sucℤ $ ℤ+-assoc m n (pos o) ⟩
    sucℤ (m + n + pos o)   ∎
  )
ℤ+-assoc m n (neg zero) = refl
ℤ+-assoc m n (neg (suc o)) = 
  ( m + predℤ (n + neg o)   ≡⟨ ℤ+-pred m (n + neg o) ⟩
    predℤ (m + (n + neg o)) ≡⟨ cong predℤ $ ℤ+-assoc m n (neg o) ⟩
    predℤ (m + n + neg o)   ∎
  )
ℤ+-assoc m n (posneg i) = refl

lemma : (m n : ℕ) → n + m * suc n ≡ m + n * suc m
lemma m n =
  ( n + m * suc n   ≡⟨ cong (n +_) $ *-suc m n ⟩
    n + (m + m * n) ≡⟨ +-assoc n m (m * n) ⟩
    n + m + m * n   ≡⟨ cong (_+ m * n) $ +-comm n m ⟩
    m + n + m * n   ≡⟨ cong (m + n +_) $ *-comm m n ⟩
    m + n + n * m   ≡⟨ sym $ +-assoc m n (n * m) ⟩
    m + (n + n * m) ≡⟨ cong (m +_) $ sym $ *-suc n m ⟩
    m + n * suc m   ∎
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
  ( neg (m + suc n)       ≡⟨ cong neg $ +-suc m n ⟩
    predℤ (neg (m + n))   ≡⟨ cong predℤ $ neg-distrib-+ m n ⟩
    predℤ (neg m + neg n) ∎
  )

pos-distrib-+ : (m n : ℕ) → pos (m + n) ≡ pos m + pos n
pos-distrib-+ m zero = cong pos $ +-zero m
pos-distrib-+ m (suc n) = 
  ( pos (m + suc n)      ≡⟨ cong pos $ +-suc m n ⟩
    sucℤ (pos (m + n))   ≡⟨ cong sucℤ $ pos-distrib-+ m n ⟩
    sucℤ (pos m + pos n) ∎
  )

lemma2 : (m n : ℕ) → suc (n + m * suc (suc n)) ≡ suc m + (n + m * suc n)
lemma2 m n = 
  ( suc (n + m * suc (suc n)) ≡⟨ cong (suc ∘ (n +_)) $ *-suc m (suc n) ⟩
    suc (n + (m + m * suc n)) ≡⟨ cong (suc ∘ (n +_)) $ +-comm m (m * suc n) ⟩
    suc (n + (m * suc n + m)) ≡⟨ cong (suc) $ +-assoc n (m * suc n) m ⟩
    suc (n + m * suc n + m)   ≡⟨ sym $ +-suc (n + m * suc n) m ⟩
    n + m * suc n + suc m     ≡⟨ +-comm (n + m * suc n) (suc m) ⟩
    suc m + (n + m * suc n)   ∎
  )

lemma3 : (m : ℤ) → (i : I) → m * 1 ≡ (m + m * posneg i)
lemma3 m i = 
  ( m * 1            ≡⟨ sym $ m≡m*ℤ1 m ⟩
    m                ≡⟨ refl ⟩
    m + 0            ≡⟨ cong (m +_) $ 0≡m*ℤ0 m ⟩
    m + m * 0        ≡⟨ cong (λ x → m + m * x) (λ j → posneg (i ∧ j)) ⟩
    m + m * posneg i ∎
  )

ℤ-m+-m≡0 : (m : ℕ) → pos m + neg m ≡ 0
ℤ-m+-m≡0 zero = refl
ℤ-m+-m≡0 (suc m) = 
  ( predℤ (pos (suc m) + neg m)  ≡⟨ cong predℤ $ ℤ+-comm (pos (suc m)) (neg m) ⟩
    predℤ (neg m + pos (suc m))  ≡⟨ refl ⟩
    predℤ (sucℤ (neg m + pos m)) ≡⟨ predSucℤ _ ⟩
    neg m + pos m                ≡⟨ ℤ+-comm (neg m) (pos m) ⟩
    pos m + neg m                ≡⟨ ℤ-m+-m≡0 m ⟩
    0                            ∎
  )

ℤ--m+m≡0 : (m : ℕ) → neg m + pos m ≡ 0
ℤ--m+m≡0 m = ℤ+-comm (neg m) (pos m) ∙ ℤ-m+-m≡0 m

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
ℤ*-suc (pos (suc m)) (neg (suc zero)) = 
  ( pos (suc m) * -0 ≡⟨ cong (pos (suc m) *_) $ sym $ posneg ⟩
    pos (suc m) * 0 ≡⟨ sym $ 0≡m*ℤ0 (pos (suc m)) ⟩
    0 ≡⟨ sym $ ℤ--m+m≡0 m ⟩
    neg m + pos m ≡⟨ sym $ predSucℤ _ ⟩
    predℤ (sucℤ (neg m + pos m)) ≡⟨ refl ⟩
    predℤ (neg m + pos (suc m)) ≡⟨ cong predℤ $ ℤ+-comm (neg m) (pos (suc m)) ⟩
    predℤ (pos (suc m) + neg m) ≡⟨ cong (predℤ ∘ (pos (suc m) +_) ∘ ℤ.neg) $ m≡m*1 m ⟩
    predℤ (pos (suc m) + neg (m * 1)) ∎
  )
ℤ*-suc (pos (suc m)) (neg (suc (suc n))) = cong predℤ $ sym
  ( predℤ (pos (suc m) + neg (n + m * suc (suc n)))  ≡⟨ cong predℤ $ ℤ+-comm (pos (suc m)) (neg (n + m * suc (suc n))) ⟩
    predℤ (neg (n + m * suc (suc n)) + pos (suc m))  ≡⟨ refl ⟩
    predℤ (sucℤ (neg (n + m * suc (suc n)) + pos m)) ≡⟨ predSucℤ (neg (n + m * suc (suc n)) + pos m) ⟩
    neg (n + m * suc (suc n)) + pos m                ≡⟨ cong ((_+ pos m) ∘ ℤ.neg ∘ (n +_)) $ *-suc m (suc n) ⟩
    neg (n + (m + m * suc n)) + pos m                ≡⟨ cong ((_+ pos m) ∘ ℤ.neg ∘ (n +_)) $ +-comm m (m * suc n) ⟩
    neg (n + (m * suc n + m)) + pos m                ≡⟨ cong ((_+ pos m) ∘ ℤ.neg) $ +-assoc n (m * suc n) m ⟩
    neg (n + m * suc n + m) + pos m                  ≡⟨ cong (_+ pos m) $ neg-distrib-+ (n + m * suc n) m ⟩
    neg (n + m * suc n) + neg m + pos m              ≡⟨ sym $ ℤ+-assoc (neg (n + m * suc n)) (neg m) (pos m) ⟩
    neg (n + m * suc n) + (neg m + pos m)            ≡⟨ cong (neg (n + m * suc n) +_) $ ℤ--m+m≡0 m ⟩
    neg (n + m * suc n) + 0                          ≡⟨ refl ⟩
    neg (n + m * suc n)                              ∎
  )
ℤ*-suc (neg (suc m)) (neg (suc zero)) = 
  ( neg (suc m) * -0 ≡⟨ cong (neg (suc m) *_) $ sym $ posneg ⟩
    neg (suc m) * 0 ≡⟨ sym $ 0≡m*ℤ0 (neg (suc m)) ⟩
    0 ≡⟨ sym $ ℤ-m+-m≡0 m ⟩
    pos m + neg m ≡⟨ sym $ sucPredℤ (pos m + neg m) ⟩
    sucℤ (predℤ (pos m + neg m)) ≡⟨ refl ⟩
    sucℤ (pos m + neg (suc m)) ≡⟨ cong sucℤ $ ℤ+-comm (pos m) (neg (suc m)) ⟩
    sucℤ (neg (suc m) + pos m) ≡⟨ cong (sucℤ ∘ (neg (suc m) +_) ∘ ℤ.pos) $ m≡m*1 m ⟩
    sucℤ (neg (suc m) + pos (m * 1)) ∎
  )
ℤ*-suc (neg (suc m)) (neg (suc (suc n))) = cong sucℤ $ sym
  ( sucℤ (predℤ (neg m) + pos (n + m * suc (suc n))) ≡⟨ cong sucℤ $ ℤ+-comm (predℤ (neg m)) (pos (n + m * suc (suc n))) ⟩
    sucℤ (pos (n + m * suc (suc n)) + predℤ (neg m)) ≡⟨ cong sucℤ $ ℤ+-pred (pos (n + m * suc (suc n))) (neg m) ⟩
    sucℤ (predℤ (pos (n + m * suc (suc n)) + neg m)) ≡⟨ sucPredℤ _ ⟩
    pos (n + m * suc (suc n)) + neg m ≡⟨ cong ((_+ neg m) ∘ ℤ.pos ∘ (n +_)) $ *-suc m (suc n) ⟩
    pos (n + (m + m * suc n)) + neg m ≡⟨ cong ((_+ neg m) ∘ ℤ.pos) $ +-assoc n m (m * suc n) ⟩
    pos (n + m + m * suc n) + neg m ≡⟨ cong ((_+ neg m) ∘ ℤ.pos ∘ (_+ m * suc n)) $ +-comm n m ⟩
    pos (m + n + m * suc n) + neg m ≡⟨ cong ((_+ neg m) ∘ ℤ.pos) $ sym $ +-assoc m n (m * suc n) ⟩
    pos (m + (n + m * suc n)) + neg m ≡⟨ cong (_+ neg m) $ pos-distrib-+ m (n + m * suc n) ⟩
    pos m + pos (n + m * suc n) + neg m ≡⟨ cong (_+ neg m) $ ℤ+-comm (pos m) (pos (n + m * suc n))  ⟩
    pos (n + m * suc n) + pos m + neg m ≡⟨ sym $ ℤ+-assoc (pos (n + m * suc n)) (pos m) (neg m) ⟩
    pos (n + m * suc n) + (pos m + neg m) ≡⟨ cong (pos (n + m * suc n) +_) $ ℤ-m+-m≡0 m ⟩
    pos (n + m * suc n) + 0 ≡⟨ refl ⟩
    pos (n + m * suc n) ∎
  )
ℤ*-suc (pos (suc m)) (pos (suc n)) = cong sucℤ
  ( pos (suc (n + m * suc (suc n)))   ≡⟨ cong ℤ.pos $ lemma2 m n ⟩
    pos (suc m + (n + m * suc n))     ≡⟨ pos-distrib-+ (suc m) (n + m * suc n) ⟩
    pos (suc m) + pos (n + m * suc n) ∎
  )
ℤ*-suc (neg (suc m)) (pos (suc n)) = cong predℤ
  ( neg (suc (n + m * suc (suc n)))   ≡⟨ cong ℤ.neg $ lemma2 m n ⟩
    neg (suc m + (n + m * suc n))     ≡⟨ neg-distrib-+ (suc m) (n + m * suc n) ⟩
    neg (suc m) + neg (n + m * suc n) ∎
  )

lemma4 : (m : ℕ) → neg (suc (m * 1)) ≡ predℤ (pos (m * 0) + neg m)
lemma4 m = cong predℤ
  ( neg (m * 1)         ≡⟨ cong ℤ.neg $ sym $ m≡m*1 m ⟩
    neg m               ≡⟨ m≡0+ℤm _ ⟩
    pos 0 + neg m       ≡⟨ cong ((_+ neg m) ∘ ℤ.pos) $ 0≡m*0 m ⟩
    pos (m * 0) + neg m ∎
  )

lemma5 : (m : ℕ) → pos (suc (m * 1)) ≡ sucℤ (neg (m * 0) + pos m)
lemma5 m = cong sucℤ
  ( pos (m * 1)         ≡⟨ cong ℤ.pos $ sym $ m≡m*1 m ⟩
    pos m               ≡⟨ m≡0+ℤm _ ⟩
    0 + pos m           ≡⟨ cong (_+ pos m) posneg ⟩
    neg 0 + pos m       ≡⟨ cong ((_+ pos m) ∘ ℤ.neg) $ 0≡m*0 m ⟩
    neg (m * 0) + pos m ∎
  )

lemma6 : (m n : ℕ) → n + m * suc (suc n) ≡ m + (n + m * suc n)
lemma6 m n =
  ( n + m * suc (suc n) ≡⟨ cong (n +_) $ *-suc m (suc n) ⟩
    n + (m + m * suc n) ≡⟨ +-assoc n m (m * suc n) ⟩
    n + m + m * suc n   ≡⟨ cong (_+ m * suc n) $ +-comm n m ⟩
    m + n + m * suc n   ≡⟨ sym $ +-assoc m n (m * suc n) ⟩
    m + (n + m * suc n) ∎
  )

lemma7 : (m n : ℕ) → m + (n + m * n) ≡ n + m * suc n
lemma7 m n =
  ( m + (n + m * n) ≡⟨ +-assoc m n (m * n) ⟩
    m + n + m * n   ≡⟨ cong (_+ m * n) $ +-comm m n ⟩
    n + m + m * n   ≡⟨ sym $ +-assoc n m (m * n) ⟩
    n + (m + m * n) ≡⟨ cong (n +_) $ sym $ *-suc m n ⟩
    n + m * suc n   ∎
  )

ℤ*-pred : (m n : ℤ) → m * predℤ n ≡ m * n - m
ℤ*-pred (pos zero) (pos zero) = sym posneg
ℤ*-pred (neg zero) (pos zero) = sym posneg
ℤ*-pred (posneg i) (pos zero) = sym posneg
ℤ*-pred (pos zero) (neg zero) = sym posneg
ℤ*-pred (neg zero) (neg zero) = sym posneg
ℤ*-pred (posneg i) (neg zero) = sym posneg
ℤ*-pred (pos zero) (posneg i) = sym posneg
ℤ*-pred (neg zero) (posneg i) = sym posneg
ℤ*-pred (posneg i) (posneg j) = sym posneg
ℤ*-pred (pos (suc m)) (pos zero) = lemma4 m
ℤ*-pred (pos (suc m)) (neg zero) = lemma4 m
ℤ*-pred (pos (suc m)) (posneg i) = lemma4 m
ℤ*-pred (neg (suc m)) (pos zero) = lemma5 m
ℤ*-pred (neg (suc m)) (neg zero) = lemma5 m
ℤ*-pred (neg (suc m)) (posneg i) = lemma5 m
ℤ*-pred (pos zero) (pos (suc n)) = refl
ℤ*-pred (neg zero) (pos (suc n)) = refl
ℤ*-pred (posneg i) (pos (suc n)) = refl
ℤ*-pred (pos zero) (neg (suc n)) = refl
ℤ*-pred (neg zero) (neg (suc n)) = refl
ℤ*-pred (posneg i) (neg (suc n)) = refl
ℤ*-pred (pos (suc m)) (pos (suc n)) = 
  ( pos (n + m * n)                            ≡⟨ m≡0+ℤm _ ⟩
    0 + pos (n + m * n)                        ≡⟨ cong (_+ pos (n + m * n)) $ sym $ ℤ--m+m≡0 m ⟩
    neg m + pos m + pos (n + m * n)            ≡⟨ sym $ ℤ+-assoc (neg m) (pos m) (pos (n + m * n)) ⟩
    neg m + (pos m + pos (n + m * n))          ≡⟨ cong (neg m +_) $ sym $ pos-distrib-+ m (n + m * n) ⟩
    neg m + pos (m + (n + m * n))              ≡⟨ cong ((neg m +_) ∘ ℤ.pos) $ lemma7 m n ⟩
    neg m + pos (n + m * suc n)                ≡⟨ cong (neg m +_) $ sym $ predSucℤ (pos (n + m * suc n)) ⟩
    neg m + predℤ (sucℤ (pos (n + m * suc n))) ≡⟨ ℤ+-pred (neg m) (sucℤ (pos (n + m * suc n))) ⟩
    predℤ (neg m + sucℤ (pos (n + m * suc n))) ≡⟨ cong predℤ $ ℤ+-comm (neg m) (sucℤ (pos (n + m * suc n))) ⟩
    predℤ (sucℤ (pos (n + m * suc n)) + neg m) ∎
  )
ℤ*-pred (neg (suc m)) (pos (suc n)) = 
  ( neg (n + m * n)                            ≡⟨ m≡0+ℤm _ ⟩
    0 + neg (n + m * n)                        ≡⟨ cong (_+ neg (n + m * n)) $ sym $ ℤ-m+-m≡0 m ⟩
    pos m + neg m + neg (n + m * n)            ≡⟨ sym $ ℤ+-assoc (pos m) (neg m) (neg (n + m * n)) ⟩
    pos m + (neg m + neg (n + m * n))          ≡⟨ cong (pos m +_) $ sym $ neg-distrib-+ m (n + m * n) ⟩
    pos m + neg (m + (n + m * n))              ≡⟨ cong ((pos m +_) ∘ ℤ.neg) $ lemma7 m n ⟩
    pos m + neg (n + m * suc n)                ≡⟨ cong (pos m +_) $ sym $ sucPredℤ (neg (n + m * suc n)) ⟩
    pos m + sucℤ (predℤ (neg (n + m * suc n))) ≡⟨ ℤ+-suc (pos m) (predℤ (neg (n + m * suc n))) ⟩
    sucℤ (pos m + predℤ (neg (n + m * suc n))) ≡⟨ cong sucℤ $ ℤ+-comm (pos m) (predℤ (neg (n + m * suc n))) ⟩
    sucℤ (predℤ (neg (n + m * suc n)) + pos m) ∎
  )
ℤ*-pred (pos (suc m)) (neg (suc n)) = cong predℤ
  ( predℤ (neg (n + m * suc (suc n)))   ≡⟨ cong (predℤ ∘ ℤ.neg) $ lemma6 m n ⟩
    predℤ (neg (m + (n + m * suc n)))   ≡⟨ cong predℤ $ neg-distrib-+ m (n + m * suc n) ⟩
    predℤ (neg m + neg (n + m * suc n)) ≡⟨ ℤ+-pred (neg m) (neg (n + m * suc n)) ⟩
    neg m + predℤ (neg (n + m * suc n)) ≡⟨ ℤ+-comm (neg m) (predℤ (neg (n + m * suc n))) ⟩
    predℤ (neg (n + m * suc n)) + neg m ∎
  )
ℤ*-pred (neg (suc m)) (neg (suc n)) = cong sucℤ
  ( sucℤ (pos (n + m * suc (suc n)))   ≡⟨ cong (sucℤ ∘ ℤ.pos) $ lemma6 m n ⟩
    sucℤ (pos (m + (n + m * suc n)))   ≡⟨ cong sucℤ $ pos-distrib-+ m (n + m * suc n) ⟩
    sucℤ (pos m + pos (n + m * suc n)) ≡⟨ sym $ ℤ+-suc (pos m) (pos (n + m * suc n)) ⟩
    pos m + sucℤ (pos (n + m * suc n)) ≡⟨ ℤ+-comm (pos m) (sucℤ (pos (n + m * suc n))) ⟩
    sucℤ (pos (n + m * suc n)) + pos m ∎
  )

lemma-ℤ*+-right-distrib : ∀ i → (q r : ℤ) → (q + r) * posneg i ≡ q * posneg i + r * posneg i
lemma-ℤ*+-right-distrib i q r =
  ( (q + r) * 0       ≡⟨ sym $ 0≡m*ℤ0 (q + r) ⟩
    0                 ≡⟨ refl ⟩
    0 + 0             ≡⟨ cong (0 +_) $ 0≡m*ℤ0 r ⟩
    0 + (r * 0)       ≡⟨ cong (_+ (r * 0)) $ 0≡m*ℤ0 q ⟩
    (q * 0) + (r * 0) ∎
  )

ℤ*+-right-distrib : (q r s : ℤ) → (q + r) * s ≡ q * s + r * s
ℤ*+-right-distrib q r (pos zero) = lemma-ℤ*+-right-distrib i0 q r
ℤ*+-right-distrib q r (neg zero) = lemma-ℤ*+-right-distrib i1 q r
ℤ*+-right-distrib q r (posneg i) = lemma-ℤ*+-right-distrib i q r
ℤ*+-right-distrib q r (pos (suc n)) = 
  ( (q + r) * sucℤ (pos n)              ≡⟨ ℤ*-suc (q + r) (pos n) ⟩
    q + r + (q + r) * pos n             ≡⟨ cong (q + r +_) $ ℤ*+-right-distrib q r (pos n) ⟩
    q + r + (q * pos n + r * pos n)     ≡⟨ ℤ+-assoc (q + r) (q * pos n) (r * pos n) ⟩
    q + r + q * pos n + r * pos n       ≡⟨ cong (_+ r * pos n) $ sym $ ℤ+-assoc q r (q * pos n) ⟩
    q + (r + q * pos n) + r * pos n     ≡⟨ cong ((_+ r * pos n) ∘ (q +_)) $ ℤ+-comm r (q * pos n) ⟩
    q + (q * pos n + r) + r * pos n     ≡⟨ cong (_+ r * pos n) $ ℤ+-assoc q (q * pos n) r ⟩
    q + q * pos n + r + r * pos n       ≡⟨ sym $ ℤ+-assoc (q + q * pos n) r (r * pos n) ⟩
    q + q * pos n + (r + r * pos n)     ≡⟨ cong (q + q * pos n +_) $ sym $ ℤ*-suc r (pos n) ⟩
    q + q * pos n + r * sucℤ (pos n)    ≡⟨ cong (_+ r * sucℤ (pos n)) $ sym $ ℤ*-suc q (pos n) ⟩
    q * sucℤ (pos n) + r * sucℤ (pos n) ∎
  )
ℤ*+-right-distrib q r (neg (suc n)) = 
  ( (q + r) * predℤ (neg n)               ≡⟨ ℤ*-pred (q + r) (neg n) ⟩
    (q + r) * (neg n) - (q + r)           ≡⟨ cong (_- (q + r)) $ ℤ*+-right-distrib q r (neg n) ⟩
    q * neg n + r * neg n - (q + r)       ≡⟨ {!!} ⟩ -- TODO: needs things like a + (- b) = a - b
    q * neg n - q + (r * neg n - r)       ≡⟨ cong (q * neg n - q +_) $ sym $ ℤ*-pred r (neg n) ⟩
    q * neg n - q + r * predℤ (neg n)     ≡⟨ cong (_+ r * predℤ (neg n)) $ sym $ ℤ*-pred q (neg n) ⟩
    q * predℤ (neg n) + r * predℤ (neg n) ∎
  )

ℤ*+-left-distrib : (q r s : ℤ) → q * (r + s) ≡ q * r + q * s
ℤ*+-left-distrib q r s =
  ( q * (r + s) ≡⟨ ℤ*-comm q (r + s) ⟩
    (r + s) * q ≡⟨ ℤ*+-right-distrib r s q ⟩
    r * q + s * q ≡⟨ cong (_+ s * q) $ ℤ*-comm r q ⟩
    q * r + s * q ≡⟨ cong (q * r +_) $ ℤ*-comm s q ⟩
    q * r + q * s ∎
  )

lemma-ℤ*-assoc : ∀ i → (m n : ℤ) → m * (n * posneg i) ≡ m * n * posneg i
lemma-ℤ*-assoc i m n =
  ( m * (n * 0)        ≡⟨ cong (m *_) $ sym $ 0≡m*ℤ0 n ⟩
    m * 0              ≡⟨ sym $ 0≡m*ℤ0 m ⟩
    0                  ≡⟨ 0≡m*ℤ0 (m * n) ⟩
    m * n * 0          ∎
  )

ℤ*-assoc : (m n o : ℤ) → m * (n * o) ≡ m * n * o
ℤ*-assoc m n (pos zero) = lemma-ℤ*-assoc i0 m n
ℤ*-assoc m n (neg zero) = lemma-ℤ*-assoc i1 m n
ℤ*-assoc m n (posneg i) = lemma-ℤ*-assoc i m n
ℤ*-assoc m n (pos (suc o)) = 
  ( m * (n * sucℤ (pos o))  ≡⟨ cong (m *_) $ ℤ*-suc n (pos o) ⟩
    m * (n + n * pos o)     ≡⟨ ℤ*+-left-distrib m n (n * pos o) ⟩
    m * n + m * (n * pos o) ≡⟨ cong (m * n +_) $ ℤ*-assoc m n (pos o) ⟩
    m * n + m * n * pos o   ≡⟨ sym $ ℤ*-suc (m * n) (pos o) ⟩
    m * n * sucℤ (pos o)    ∎
  )
ℤ*-assoc m n (neg (suc o)) = 
  ( m * (n * predℤ (neg o)) ≡⟨ cong (m *_) $ ℤ*-pred n (neg o) ⟩
    m * (n * neg o - n)     ≡⟨ {!!} ⟩ -- TODO: needs things like a + (- b) = a - b
    m * (n * neg o) - m * n ≡⟨ cong (_- m * n) $ ℤ*-assoc m n (neg o) ⟩
    m * n * neg o - m * n   ≡⟨ sym $ ℤ*-pred (m * n) (neg o) ⟩
    m * n * predℤ (neg o)   ∎
  )

instance
  ℚ+ : Op+ ℚ ℚ (const₂ ℚ)
  _+_ ⦃ ℚ+ ⦄ q r = q plus r where
    plus_lemma1 : (u a v b w c : ℤ)
      (x : ¬ a ≡ 0) (p₁ : ¬ b ≡ 0) (p₂ : ¬ c ≡ 0)
      (y : v * c ≡ w * b)
      → con (u * b + v * a) (a * b) (nonzero-prod a b x p₁) ≡ con (u * c + w * a) (a * c) (nonzero-prod a c x p₂)
    plus_lemma1 u a v b w c x p₁ p₂ y = path _ _ _ _
      ( (u * b + v * a) * (a * c)         ≡⟨ ℤ*+-right-distrib (u * b) (v * a) (a * c) ⟩
        u * b * (a * c) + v * a * (a * c) ≡⟨ cong (_+ (v * a * (a * c))) $
          u * b * (a * c)                   ≡⟨ sym $ ℤ*-assoc u b (a * c) ⟩
          u * (b * (a * c))                 ≡⟨ cong (u *_) $ ℤ*-comm b (a * c) ⟩
          u * (a * c * b)                   ≡⟨ cong ((u *_) ∘ (_* b)) $ ℤ*-comm a c ⟩
          u * (c * a * b)                   ≡⟨ cong (u *_) $ sym $ ℤ*-assoc c a b ⟩
          u * (c * (a * b))                 ≡⟨ ℤ*-assoc u c (a * b) ⟩
          u * c * (a * b)                   ∎
        ⟩
        u * c * (a * b) + v * a * (a * c) ≡⟨ cong (u * c * (a * b) +_) $
          v * a * (a * c)                   ≡⟨ sym $ ℤ*-assoc v a (a * c) ⟩
          v * (a * (a * c))                 ≡⟨ cong (v *_) $ ℤ*-comm a (a * c) ⟩
          v * (a * c * a)                   ≡⟨ cong ((v *_) ∘ (_* a)) $ ℤ*-comm a c ⟩
          v * (c * a * a)                   ≡⟨ cong (v *_) $ sym $ ℤ*-assoc c a a ⟩
          v * (c * (a * a))                 ≡⟨ ℤ*-assoc v c (a * a) ⟩
          v * c * (a * a)                   ≡⟨ cong (_* (a * a)) y ⟩
          w * b * (a * a)                   ≡⟨ sym $ ℤ*-assoc w b (a * a) ⟩
          w * (b * (a * a))                 ≡⟨ cong (w *_) $ ℤ*-assoc b a a ⟩
          w * (b * a * a)                   ≡⟨ cong ((w *_) ∘ (_* a)) $ ℤ*-comm b a ⟩
          w * (a * b * a)                   ≡⟨ cong (w *_) $ ℤ*-comm (a * b) a ⟩
          w * (a * (a * b))                 ≡⟨ ℤ*-assoc w a (a * b) ⟩
          w * a * (a * b)                   ∎
        ⟩
        u * c * (a * b) + w * a * (a * b) ≡⟨ sym $ ℤ*+-right-distrib (u * c) (w * a) (a * b) ⟩
        (u * c + w * a) * (a * b)         ∎
      )
    
    plus_lemma2 : (u a v b w c : ℤ)
      (x : ¬ a ≡ 0) (p₁ : ¬ b ≡ 0) (p₂ : ¬ c ≡ 0)
      (y : v * c ≡ w * b)
      → con (v * a + u * b) (b * a) (nonzero-prod b a p₁ x) ≡ con (w * a + u * c) (c * a) (nonzero-prod c a p₂ x)
    plus_lemma2 u a v b w c x p₁ p₂ y = -- trying to reuse plus_lemma1 with this proof
      con (v * a + u * b) (b * a) _ ≡⟨ cong (λ nom → con nom (b * a) _) $ ℤ+-comm (v * a) (u * b) ⟩
      con (u * b + v * a) (b * a) _ ≡⟨ cong₂ (λ denom prf → con (u * b + v * a) denom prf) (ℤ*-comm b a) $ {!!} ⟩ -- TODO: not sure if this is the right approach
      con (u * b + v * a) (a * b) (nonzero-prod a b x p₁) ≡⟨ plus_lemma1 u a v b w c x p₁ p₂ y ⟩
      con (u * c + w * a) (a * c) (nonzero-prod a c x p₂) ≡⟨ cong₂ (λ denom prf → con (u * c + w * a) denom prf) (ℤ*-comm a c) $ {!!} ⟩ -- TODO: ditto
      con (u * c + w * a) (c * a) (nonzero-prod c a p₂ x) ≡⟨ cong (λ nom → con nom (c * a) (nonzero-prod c a p₂ x)) $ ℤ+-comm (u * c) (w * a) ⟩
      con (w * a + u * c) (c * a) _ ∎
    
    _plus_ : ℚ → ℚ → ℚ
    con u a x plus con v b y = con (u * b + v * a) (a * b) (nonzero-prod a b x y)
    con u a x plus path v b w c {p₁} {p₂} y i = plus_lemma1 u a v b w c x p₁ p₂ y i
    path v b w c {p₁} {p₂} y i plus con u a x = plus_lemma2 u a v b w c x p₁ p₂ y i
    path u a v b {p} {q} x i plus path u₁ a₁ v₁ b₁ {p₁} {q₁} x₁ j = ?
      -- attempts below:
      {-
      hcomp (λ k → \ { (i = i0) → plus_lemma1 u a u₁ a₁ v₁ b₁ p p₁ q₁ x₁ (j ∧ k)
                     ; (i = i1) → plus_lemma1 v b u₁ a₁ v₁ b₁ q p₁ q₁ x₁ (j ∧ k)
                     ; (j = i0) → plus_lemma2 u₁ a₁ u a v b p₁ p q x i
                     ; (j = i1) → doubleCompPath-filler ({!plus_lemma1 u a u₁ a₁ v₁ b₁ p p₁ q₁ x₁!}) (plus_lemma2 v₁ b₁ u a v b q₁ p q x) {!!} i (~ k) --plus_lemma2 v₁ b₁ u a v b q₁ p q x {!k!}
                     })
            (plus_lemma2 u₁ a₁ u a v b p₁ p q x i)
      -}
      
      {-
      doubleCompPath-filler
        (sym $ plus_lemma1 u a u₁ a₁ v₁ b₁ p p₁ q₁ x₁)
        (plus_lemma2 u₁ a₁ u a v b p₁ p q x)
        (plus_lemma1 v b u₁ a₁ v₁ b₁ q p₁ q₁ x₁)
      -}
      
      {-
      hcomp (λ k → \ { (i = i0) → plus_lemma1 u a u₁ a₁ v₁ b₁ p p₁ q₁ x₁ (j ∧ k)
                     ; (i = i1) → {!compPath-filler (plus_lemma2 u₁ a₁ u a v b p₁ p q x) (plus_lemma1 v b u₁ a₁ v₁ b₁ q p₁ q₁ x₁) j k!}
                     ; (j = i0) → plus_lemma2 u₁ a₁ u a v b p₁ p q x (i ∧ k)
                     ; (j = i1) → compPath-filler (plus_lemma1 u a u₁ a₁ v₁ b₁ p p₁ q₁ x₁) (plus_lemma2 v₁ b₁ u a v b q₁ p q x) i k
                     })
            (con (u * a₁ + u₁ * a) (a * a₁) (nonzero-prod a a₁ p p₁))
      -}
    q@(path _ _ _ _ _ _) plus trunc r r₁ x y i i₁ = trunc (q plus r) (q plus r₁) (cong (q plus_) x) (cong (q plus_) y) i i₁
    q@(con _ _ _) plus trunc r r₁ x y i i₁ = trunc (q plus r) (q plus r₁) (cong (q plus_) x) (cong (q plus_) y) i i₁
    trunc q q₁ x y i i₁ plus r = trunc (q plus r) (q₁ plus r) (cong (_plus r) x) (cong (_plus r) y) i i₁

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

instance
  ℚ< : Op< ℚ ℚ (const₂ Bool)
  _<_ ⦃ ℚ< ⦄ n m = n less-than m where
    _less-than_ : ℚ → ℚ → Bool
    con u a _ less-than con v b _ = u * b < v * a
    q@(con u a x) less-than path v b w c y i = {!!} -- not sure
    path u a v b x i less-than r = {!!}
    q@(con _ _ _) less-than trunc r r₁ x y i i₁ = isSetBool (q less-than r) (q less-than r₁) (cong (q less-than_) x) (cong (q less-than_) y) i i₁
    trunc q q₁ x y i i₁ less-than r = isSetBool (q less-than r) (q₁ less-than r) (cong (_less-than r) x) (cong (_less-than r) y) i i₁

instance
  ℚ> : Op> ℚ ℚ (const₂ Bool)
  _>_ ⦃ ℚ> ⦄ n m = m < n

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

-- The reason for all of the above machinery:
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

