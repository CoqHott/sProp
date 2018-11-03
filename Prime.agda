{-# OPTIONS --prop --postfix-projections #-}

open import Basics
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)
open import Agda.Builtin.Equality

record ΣP {ℓ} {ℓ′} (A : Prop ℓ) (B : A → Prop ℓ′) : Prop (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open ΣP public

record ⊤ : Prop where constructor tt
data ⊥ : Prop where

syntax ΣP A (λ x → B) = x ∈ A & B

_&_ : Prop → Prop → Prop
A & B = x ∈ A & B

_≤_ : Nat → Nat → Prop
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

_<_ : Nat → Nat → Prop
x < y = suc x ≤ y

≤-0 : ∀ {n} → 0 ≤ n
≤-0 = _

≤-suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
≤-suc p = p

module ≤-elim {ℓ}
              (P     : ∀ m n → m ≤ n → Set ℓ)
              (p-0   : ∀ {n} → P 0 n (≤-0 {n}))
              (p-suc : ∀ {m n e} → P m n e
                     → P (suc m) (suc n) (≤-suc {m} {n} e)) where

  ≤-elim : (m n : Nat) (H : m ≤ n) → P m n H
  ≤-elim zero    n       H = p-0
  ≤-elim (suc m) (suc n) H = p-suc (≤-elim m n H)

open ≤-elim public

minus-correct : ∀ {m n} → n ≤ m → n + (m - n) ≡ m
minus-correct {zero}  {zero}  p = refl
minus-correct {suc m} {zero}  p = refl
minus-correct {suc m} {suc n} p = cong suc (minus-correct {m = m} {n = n} p)

infix 80 _∣_

{-# TERMINATING #-}
_∣_ : Nat → Nat → Prop
m     ∣ zero  = ⊤
zero  ∣ suc n = ⊥
suc m ∣ suc n = (suc m ≤ suc n) & (suc m ∣ (n - m))

divide-0 : ∀ {n} → n ∣ 0
divide-0 = _

divide-suc : ∀ {m n} → suc m ≤ suc n → suc m ∣ (suc n - suc m) → suc m ∣ suc n
divide-suc e p = e , p

module divide-elim {ℓ}
                   (P     : ∀ m n → m ∣ n → Set ℓ)
                   (p-0   : ∀ {m} → P m 0 (divide-0 {m}))
                   (p-suc : ∀ {m n e d} → P (suc m) (n - m) d
                          → P (suc m) (suc n) (divide-suc e d)) where

  {-# TERMINATING #-}
  divide-elim : (m n : Nat) (H : m ∣ n) → P m n H
  divide-elim m zero H = p-0
  divide-elim (suc m) (suc n) H = p-suc {e = H .π₁} (divide-elim (suc m) (n - m) (H .π₂))

open divide-elim public

divide-to-nat : ∀ {m n} → m ∣ n → Nat
divide-to-nat = divide-elim (λ _ _ _ → Nat) 0 suc _ _

divide-to-nat-correct : ∀ {m n} → (e : m ∣ n) → divide-to-nat e * m ≡ n
divide-to-nat-correct = divide-elim (λ m n e → divide-to-nat e * m ≡ n)
  refl
  (λ {m} {n} {e} {d} H → cong suc
    (cong (m +_) H ⟨≡⟩ minus-correct {n} {m} e))
  _ _

record GCD (a b g : Nat) : Prop where
  field
    divisor-left  : g ∣ a
    divisor-right : g ∣ b
    most-general  : ∀ x → x ∣ a → x ∣ b → x ∣ g
open GCD public

RelPrime : Nat → Nat → Prop
RelPrime a b = GCD a b 1

record Prime (p : Nat) : Prop where
  field
    over-one : 2 ≤ p
    is-prime : ∀ n → 1 ≤ n → suc n ≤ p → RelPrime n p
open Prime public

prime-13 : Prime 13
prime-13 = λ where
    .over-one → _
    .is-prime → λ where
      1  _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general _ p _ → p
      2  _ _ → λ where
        .divisor-left  → _
        .divisor-right → _
        .most-general  → λ where
          1 _ _ → _
          2 _ ()
      3  _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          3 _ ()
      4  _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          4 _ ()
      5  _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          5 _ ()
      6  _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          6 _ ()
      7  _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          7 _ ()
      8  _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          8 _ ()
      9  _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          9 _ ()
      10 _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          10 _ ()
      11 _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          11 _ ()
      12 _ _ → λ where
        .divisor-left → _
        .divisor-right → _
        .most-general → λ where
          1 _ _ → _
          12 _ ()
