-- EAFIT 2017
--
-- Andreas Abel,
--
--   Type Theory
--
-- Session 4

type = Set

-- Natural numbers

data ℕ : Set where  -- \ b n
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- plus

plus : ℕ → ℕ → ℕ  -- \to
plus zero    y = y
plus (suc x) y = suc (plus x y)

-- Load: C-c C-l
-- Split: C-c C-c
-- Show context: C-c C-,
-- Refine: C-c C-r
-- Give: C-c C-SPC

-- List

data List (A : Set) : Set where
  nil  : List A
  cons : (x : A) (xs : List A) → List A

mynil : List ℕ
mynil = nil {ℕ}

-- Vectors

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} (x : A) (xs : Vec A n) → Vec A (suc n)  -- _ \ : : _

v1 : Vec ℕ 1
v1 = zero ∷ []

v2 = _∷_ {n = suc zero} zero v1

-- C-c C-=  Show constraints
-- C-c C-s  Solve

-- append

append : ∀ {A n m} → Vec A n → Vec A m → Vec A (plus n m)
append []       ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

-- C-c C-.  Infer type of hole

-- Fin

data Fin : ℕ → Set where
  zero : ∀{n} → Fin (ℕ.suc n)
  suc  : ∀{n} → Fin n → Fin (ℕ.suc n)

-- lookup

lookup : ∀{A n} → Vec A n → Fin n → A
-- lookup [] ()
lookup (x ∷ xs) Fin.zero    = x
lookup (x ∷ xs) (Fin.suc i) = lookup xs i

-- lookup' : ∀{A} n → Vec A n → Fin n → A
-- lookup' .(suc n) xs (zero {n}) = {!!}
-- lookup' .(suc _) (x ∷ xs) (suc i) = {!!}

-- Equality

data _≡_ {A : Set} (x : A) : A → Set where   -- \equiv   or   \ = =
  refl : x ≡ x

Eq : {A : Set} → A → A → Set
Eq = _≡_

sym : ∀{A} (x y : A) → x ≡ y → y ≡ x
sym x .x refl = refl

cong : ∀{A B} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- C-c C-r refine

-- substitution

subst : ∀{A : Set} (P : A → Set) {x y : A} (p : x ≡ y) (h : P x) → P y
subst P {x} {.x} refl h = h

-- C-c C-a auto

-- associativity of plus

assoc-plus : ∀{n m k} → plus (plus n m) k ≡ plus n (plus m k)
assoc-plus {zero}  = refl
assoc-plus {suc n} = cong suc (assoc-plus {n})

-- Sigma

data Σ (A : Set) (B : A → Set) : Set where

-- Booleans

-- Disjoint union

-- Lists

-- filtering
