open import Agda.Primitive public
open import Agda.Builtin.Unit
import Agda.Builtin.Nat
module Builtin = Agda.Builtin.Nat
open import Agda.Builtin.FromNat public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Size public

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

infixr 0 _⟨≡⟩_
_⟨≡⟩_ = trans

transport : ∀ {a b} {A : Set a} (B : A → Set b) {x y} → x ≡ y → B x → B y
transport B refl bx = bx

data Empty : Set where

data DecSet {a} (P : Set a) : Set a where
  yes : P → DecSet P
  no  : (P → Empty) → DecSet P

record Eq {a} (A : Set a) : Set a where
  infix 4 _==_
  field
    _==_ : (x y : A) → DecSet (x ≡ y)

open Eq {{...}} public

infixr 0 case_of_
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

instance
  NumberNat : Number Builtin.Nat
  NumberNat .Number.Constraint _ = ⊤
  NumberNat .fromNat n = n
