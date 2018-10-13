{-# OPTIONS --prop --postfix-projections --experimental-irrelevance --without-K #-}

open import Agda.Primitive
open import Agda.Builtin.Size
open import Agda.Builtin.FromNat
import Agda.Builtin.Nat

import Prelude.Decidable
import Prelude.Empty

open import Prelude.Equality
open import Prelude.Function

record Lift {ℓ} (P : Prop ℓ) : Set ℓ where
  constructor lift
  field lower : P

record ⊤ : Prop where constructor tt
data ⊥ : Prop where

ex-falso : ∀ {ℓ} {P : Prop ℓ} → ⊥ → P
ex-falso ()

¬_ : ∀ {ℓ} → Prop ℓ → Prop ℓ
¬ P = P → ⊥

record ΣP {ℓ} {ℓ′} (A : Prop ℓ) (B : A → Prop ℓ′) : Prop (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open ΣP public

syntax ΣP A (λ x → B) = x ∈ A & B

_&_ : Prop → Prop → Prop
A & B = x ∈ A & B

data Dec {ℓ} (P : Prop ℓ) : Set ℓ where
  yes : P   → Dec P
  no  : ¬ P → Dec P

FromDec : ∀ {ℓ} {P : Prop ℓ} → Dec P → Prop ℓ
FromDec {P = P} (yes _) = P
FromDec {P = P} (no  _) = ¬ P

fromDec : ∀ {ℓ} {P : Prop ℓ} (d : Dec P) → FromDec d
fromDec (yes x) = x
fromDec (no  x) = x

rew→ : ∀ {a b} {A : Set a} (B : A → Prop b) {x y} → x ≡ y → B x → B y
rew→ B refl bx = bx

rew← : ∀ {a b} {A : Set a} (B : A → Prop b) {x y} → x ≡ y → B y → B x
rew← B refl by = by

data Nat ..{i : Size} : Set where
  zero : Nat {i}
  suc  : .{j : Size< i} → Nat {j} → Nat {i}

instance
  _ : Number Nat
  _ = λ where
      .Number.Constraint _ → Lift ⊤
      .Number.fromNat    n → convert n
    where
      convert : Agda.Builtin.Nat.Nat → Nat
      convert Agda.Builtin.Nat.zero = zero
      convert (Agda.Builtin.Nat.suc x) = suc {∞} (convert x)

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

plus-zero : ∀ {m} → m + zero ≡ m
plus-zero {zero} = refl
plus-zero {suc m} = cong suc (plus-zero {m})

plus-suc : ∀ {m n} → m + (suc n) ≡ suc (m + n)
plus-suc {zero} {n} = refl
plus-suc {suc m} {n} = cong suc (plus-suc {m} {n})

plus-comm : ∀ {m n} → m + n ≡ n + m
plus-comm {zero} {n} = sym (plus-zero {n})
plus-comm {suc m} {n} = transport (suc (m + n) ≡_) (sym (plus-suc {n} {m})) (cong suc (plus-comm {m} {n}))

_*_ : Nat → Nat → Nat
zero * n = zero
suc m * n = n + (m * n)

_-_ : ∀ .{i} → Nat {i} → Nat → Nat {i}
m     - zero  = m
zero  - suc n = zero
suc m - suc n = m - n

_≤_ : Nat → Nat → Prop
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

_<_ : Nat → Nat → Prop
x < y = suc x ≤ y

≤-0 : ∀ {n : Nat {∞}} → 0 ≤ n
≤-0 = _

≤-suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
≤-suc p = p

≤-refl : ∀ {m} → m ≤ m
≤-refl {zero}  = _
≤-refl {suc m} = ≤-refl {m}

≤-plus-left : ∀ {k l m} → k ≤ l → k ≤ (l + m)
≤-plus-left {zero} {l} {m} k≤l = _
≤-plus-left {suc k} {suc l} {m} k≤l = ≤-plus-left {k} {l} k≤l

≤-plus-right : ∀ {k l m} → k ≤ m → k ≤ (l + m)
≤-plus-right {zero} {l} {m} k≤m = _
≤-plus-right {suc k} {l} {suc m} k≤m = rew← (suc k ≤_) (plus-suc {l} {m}) (≤-plus-right {k} {l} {m} k≤m)

not-≤ : ∀ {m n} → ¬ (m ≤ n) → n ≤ m
not-≤ {zero} {n} ¬m≤n = ex-falso (¬m≤n _)
not-≤ {suc m} {zero} ¬m≤n = _
not-≤ {suc m} {suc n} ¬m≤n = not-≤ {m} {n} ¬m≤n

≤-asym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-asym {zero}  {zero}  p q = refl
≤-asym {suc m} {suc n} p q = cong suc (≤-asym p q)

module ≤-elim {ℓ}
              (P     : ∀ m n → m ≤ n → Set ℓ)
              (p-0   : ∀ {n} → P 0 n (≤-0 {n}))
              (p-suc : ∀ {m n e} → P m n e
                     → P (suc m) (suc n) (≤-suc {m} {n} e)) where

  ≤-elim : (m n : Nat) (H : m ≤ n) → P m n H
  ≤-elim zero    n       H = p-0
  ≤-elim (suc m) (suc n) H = p-suc (≤-elim m n H)

open ≤-elim public

module ≤-elimP {ℓ}
               (P     : ∀ m n → m ≤ n → Prop ℓ)
               (p-0   : ∀ {n} → P 0 n (≤-0 {n}))
               (p-suc : ∀ {m n e} → P m n e
                     → P (suc m) (suc n) (≤-suc {m} {n} e)) where

  ≤-elimP : (m n : Nat) (H : m ≤ n) → P m n H
  ≤-elimP zero    n       H = p-0
  ≤-elimP (suc m) (suc n) H = p-suc (≤-elimP m n H)

open ≤-elimP public


minus-correct : ∀ .{i} {m : Nat {i}} {n : Nat} → n ≤ m → n + (m - n) ≡ m
minus-correct {m = zero}  {zero}  p = refl
minus-correct {m = suc m} {zero}  p = refl
minus-correct {i} {m = suc {j₁} m} {suc {j₂} n} p = cong suc (minus-correct {n = n} p)

minus-refl : ∀ {m} → m - m ≡ 0
minus-refl {zero}  = refl
minus-refl {suc m} = minus-refl {m}

minus-distr-left : ∀ {k l m} → m ≤ k → (k + l) - m ≡ (k - m) + l
minus-distr-left {k} {l} {zero} m≤k = refl
minus-distr-left {suc k} {l} {suc m} m≤k = minus-distr-left {k} {l} {m} m≤k

minus-distr-right : ∀ {k l m} → m ≤ l → (k + l) - m ≡ k + (l - m)
minus-distr-right {k} {l} {zero} m≤l = refl
minus-distr-right {k} {suc l} {suc m} m≤l =
  transport (λ x → (x - suc m) ≡ (k + (l - m))) (sym (plus-suc {k} {l}))
    (minus-distr-right {k} {l} {m} m≤l)

pred : ∀ .{i} → Nat {i} → Nat {i}
pred zero    = zero
pred (suc x) = x

decEq : (x y : Nat) → Prelude.Decidable.Dec (x ≡ y)
decEq zero zero = Prelude.Decidable.yes refl
decEq zero (suc y) = Prelude.Decidable.no λ ()
decEq (suc x) zero = Prelude.Decidable.no λ ()
decEq (suc x) (suc y) = case (decEq x y) of λ where
  (Prelude.Decidable.yes x≡y) → Prelude.Decidable.yes (cong suc x≡y)
  (Prelude.Decidable.no  x≢y) → Prelude.Decidable.no λ sx≡sy → x≢y (cong pred sx≡sy)

instance
  _ : Eq Nat
  _ = λ where
      .Eq._==_ x y → decEq x y

infix 80 _∣_

_∣_ : .{i : Size} → Nat → Nat {i} → Prop
m     ∣ zero  = ⊤
zero  ∣ suc n = ⊥
suc m ∣ suc n = (suc m ≤ suc n) & (suc m ∣ (n - m))

divide-0 : ∀ {n} → n ∣ 0
divide-0 = _

divide-suc : ∀ {m n} → suc m ≤ suc n → suc m ∣ (suc n - suc m) → suc m ∣ suc n
divide-suc e p = e , p

divide-refl : ∀ .{i} {m : Nat {i}} → m ∣ m
divide-refl {m = zero} = _
divide-refl {m = suc {j} m} = ≤-refl {m} , rew← (suc m ∣_) (minus-refl {m}) _

module divide-elim {ℓ}
                   (P     : ∀ m n → m ∣ n → Set ℓ)
                   (p-0   : ∀ {m} → P m 0 (divide-0 {m}))
                   (p-suc : ∀ {m n e d} → P (suc m) (n - m) d
                          → P (suc m) (suc n) (divide-suc e d)) where

  divide-elim : ∀ {i} (m : Nat) (n : Nat {i}) (H : m ∣ n) → P m n H
  divide-elim m zero H = p-0
  divide-elim (suc m) (suc n) H = p-suc {e = H .π₁} (divide-elim (suc m) (n - m) (H .π₂))

open divide-elim public

module divide-elimP {ℓ}
                    (P     : ∀ m n → m ∣ n → Prop ℓ)
                    (p-0   : ∀ {m} → P m 0 (divide-0 {m}))
                    (p-suc : ∀ {m n e d} → P (suc m) (n - m) d
                          → P (suc m) (suc n) (divide-suc e d)) where

  divide-elimP : ∀ {i} (m : Nat) (n : Nat {i}) (H : m ∣ n) → P m n H
  divide-elimP m zero H = p-0
  divide-elimP (suc m) (suc n) H = p-suc {e = H .π₁} (divide-elimP (suc m) (n - m) (H .π₂))

open divide-elimP public

divide-to-nat : ∀ {m n} → m ∣ n → Nat
divide-to-nat = divide-elim (λ _ _ _ → Nat) zero suc _ _

divide-to-nat-correct : ∀ {m n} → (e : m ∣ n) → divide-to-nat e * m ≡ n
divide-to-nat-correct = divide-elim (λ m n e → divide-to-nat e * m ≡ n)
  refl
  (λ {m} {n} {e} {d} H → cong suc
    (cong (m +_) H ⟨≡⟩ minus-correct {m = n} {n = m} e))
  _ _

divide-plus : ∀ .{i} {m : Nat {i}} {n g} → g ∣ m → g ∣ n → g ∣ (m + n)
divide-plus {m = zero} {n} {g} g∣m g∣n = g∣n
divide-plus {m = suc m} {n} {suc g} g∣m g∣n =
  ≤-plus-left {g} {m} {n} (g∣m .π₁) ,
  rew← (suc g ∣_) (minus-distr-left {m} {n} {g} (g∣m .π₁))
    (divide-plus {m = m - g} {n} {suc g} (g∣m .π₂) g∣n)

divide-plus-left : ∀ .{i} {m} {n : Nat {i}} {g} → g ∣ (m + n) → g ∣ n → g ∣ m
divide-plus-left {m = m} {zero} {g} g∣m+0 g∣n = rew→ (g ∣_) (plus-zero {m}) g∣m+0
divide-plus-left {m = m} {suc {j} n} {suc g} g∣m+n g∣n =
  divide-plus-left {j} {m = m} {n = _-_ {j} n g} {g = suc g}
    (rew→ (suc g ∣_) (minus-distr-right {m} {n} {g} (g∣n .π₁))
      (rew→ (suc g ∣_) (plus-suc {m} {n}) g∣m+n .π₂))
    (g∣n .π₂)

divide-plus-right : ∀ {m n g} → g ∣ m → g ∣ (m + n) → g ∣ n
divide-plus-right {m} {n} {g} g∣m g∣m+n =
  divide-plus-left {m = n} {m} {g}
    (rew→ (g ∣_) (plus-comm {m} {n}) g∣m+n)
    g∣m

divide-minus : ∀ {m n g} → m ≤ n → g ∣ m → g ∣ n → g ∣ (n - m)
divide-minus {m} {n} {g} m≤n p q =
  divide-plus-right p
    (rew← (g ∣_) (minus-correct {m = n} {m} m≤n) q)

divide-minus-inv : ∀ {m n g} → m ≤ n → g ∣ m → g ∣ (n - m) → g ∣ n
divide-minus-inv {m} {n} {g} m≤n p q =
  rew→ (g ∣_) (minus-correct {m = n} {n = m} m≤n)
    (divide-plus p q)

divide-asym : ∀ {m n} → m ∣ n → n ∣ m → m ≡ n
divide-asym {zero} {zero} p q = refl
divide-asym {suc m} {suc n} p q = ≤-asym (p .π₁) (q .π₁)

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
    is-prime : ∀ n → 1 ≤ n → n < p → RelPrime n p
open Prime public

_≤?_ : ∀ m n → Dec (m ≤ n)
zero  ≤? n     = yes _
suc m ≤? zero  = no λ ()
suc m ≤? suc n = m ≤? n

_∣?_ : ∀ .{i} m (n : Nat {i}) → Dec (m ∣ n)
m ∣? zero = yes _
zero  ∣? suc n = no λ ()
suc m ∣? suc n with (suc m ≤? suc n) | (suc m ∣? (n - m))
... | yes m≤n | yes m∣n-m = yes (m≤n , m∣n-m)
... | no ¬m≤n | _         = no λ p → ¬m≤n   (p .π₁)
... | _       | no ¬m∣n-m = no λ p → ¬m∣n-m (p .π₂)

gcd : ∀ .{i₁ i₂} (a : Nat {i₁}) (b : Nat {i₂}) → Nat
gcd           zero         b            = b
gcd           (suc a)      zero         = suc a
gcd {i₁} {i₂} (suc {j₁} a) (suc {j₂} b) with a ≤? b
... | yes _ = gcd {i₁} {j₂} (suc a) (b - a)
... | no  _ = gcd {j₁} {i₂} (a - b) (suc b)

gcd-plus-left : ∀ {a b g} → GCD a b g → GCD (a + b) b g
gcd-plus-left {a} {b} {g} p = λ where
  .divisor-left → divide-plus (p .divisor-left) (p .divisor-right)
  .divisor-right → p .divisor-right
  .most-general x x∣a+b x∣b → p .most-general x (divide-plus-left x∣a+b x∣b) x∣b

gcd-plus-right : ∀ {a b g} → GCD a b g → GCD a (a + b) g
gcd-plus-right {a} {b} {g} p = λ where
  .divisor-left → p .divisor-left
  .divisor-right → divide-plus (p .divisor-left) (p .divisor-right)
  .most-general x x∣a x∣a+b → p .most-general x x∣a (divide-plus-right x∣a x∣a+b)

gcd-minus-left : ∀ {a b g} → b ≤ a → GCD a b g → GCD (a - b) b g
gcd-minus-left {a} {b} {g} b≤a p = λ where
  .divisor-left → divide-minus {b} {a} {g} b≤a (p .divisor-right) (p .divisor-left)
  .divisor-right → p .divisor-right
  .most-general x x∣a-b x∣b → p .most-general x (divide-minus-inv {b} {a} {x} b≤a x∣b x∣a-b) x∣b

gcd-minus-right : ∀ {a b g} → a ≤ b → GCD a b g → GCD a (b - a) g
gcd-minus-right {a} {b} {g} a≤b p = λ where
  .divisor-left → p .divisor-left
  .divisor-right → divide-minus a≤b (p .divisor-left) (p .divisor-right)
  .most-general x x∣a x∣b-a → p .most-general x x∣a (divide-minus-inv {a} {b} {x} a≤b x∣a x∣b-a)

gcd-correct : ∀ .{i₁ i₂} (a : Nat {i₁}) (b : Nat {i₂}) → GCD a b (gcd a b)
gcd-correct zero b = λ where
  .divisor-left  → _
  .divisor-right → divide-refl
  .most-general  → λ _ _ x∣b → x∣b
gcd-correct (suc a) zero = λ where
  .divisor-left  → divide-refl
  .divisor-right → _
  .most-general  → λ _ x∣a _ → x∣a
gcd-correct {i₁} {i₂} (suc {j₁} a) (suc {j₂} b)
  with a ≤? b
     | gcd-correct {i₁} {j₂} (suc a) (b - a)
     | gcd-correct {j₁} {i₂} (a - b) (suc b)
... | yes a≤b | IH₁ | IH₂ =
  rew→ (λ x → GCD (suc a) x (gcd (suc a) (b - a)))
       (minus-correct {m = suc b} {n = suc a} a≤b)
       (gcd-plus-right IH₁)
... | no ¬a≤b | IH₁ | IH₂ =
  rew→ (λ x → GCD x (suc b) (gcd (a - b) (suc b)))
       (plus-suc {a - b} {b}
         ⟨≡⟩ cong suc (plus-comm {a - b} {b})
         ⟨≡⟩ minus-correct {m = suc a} {n = suc b} (not-≤ {a} {b} ¬a≤b))
       (gcd-plus-left IH₂)

gcd-unique : ∀ .{i₁ i₂} (a : Nat {i₁}) (b : Nat {i₂})
             {g : Nat} → GCD a b g → g ≡ gcd a b
gcd-unique zero b p =
  divide-asym
    (p .divisor-right)
    (p .most-general b _ divide-refl)
gcd-unique (suc a) zero p =
  divide-asym
    (p .divisor-left)
    (p .most-general (suc a)
      ( ≤-refl {a} , rew← (suc a ∣_) (minus-refl {a}) _)
      divide-refl)
gcd-unique {i₁} {i₂} (suc {j₁} a) (suc {j₂} b) {g} p with a ≤? b
... | yes a≤b = gcd-unique {i₁} {j₂} (suc a) (b - a) {g} (gcd-minus-right a≤b p)
... | no ¬a≤b = gcd-unique {j₁} {i₂} (a - b) (suc b) {g} (gcd-minus-left (not-≤ {a} {b} ¬a≤b) p)

RelPrime? : (a b : Nat) → Dec (RelPrime a b)
RelPrime? a b = case (gcd a b == 1) of λ where
    (Prelude.Decidable.yes gcd≡1) → yes (rew→ (GCD a b) gcd≡1 (gcd-correct a b))
    (Prelude.Decidable.no  gcd≢1) → no (λ gcd1 → from-⊥-in-set (gcd≢1 (sym (gcd-unique a b {1} gcd1))))
  where
    from-⊥-in-set : Prelude.Empty.⊥ → ⊥
    from-⊥-in-set ()

private
  prime-aux : ∀ p b → Dec (∀ n → b ≤ n → n < p → RelPrime n p)
  prime-aux p b = {!!}

Prime? : (p : Nat) → Dec (Prime p)
Prime? p with 2 ≤? p | prime-aux p 1
... | no  2≰p | _            = no (λ p-prime → 2≰p (p-prime .over-one))
... | _       | no q         = no (λ p-prime → q (p-prime .is-prime))
... | yes 2≤p | yes is-prime = yes λ where
    .over-one → ?
    .is-prime → ?


-- -}
