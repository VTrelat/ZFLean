/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

import ZFLean.Naturals
import ZFLean.Booleans
import ZFLean.Integers
import ZFLean.Rationals
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-! # Transferring goals to the mathlib types -/

open ZFSet

/-! ## Higher-order statements -/

/-- A curried binary operation on `ZFNat` becomes one on `ℕ`: `f : ℕ → ℕ → ℕ`, with its defining
equation. -/
example (f : ZFNat → ZFNat → ZFNat) (hf : ∀ a b, f a b = a + b) :
    ∀ a b c, f (f a b) c = f a (f b c) := by
  transfer ZFNat → ℕ =>
    intro a b c
    simp only [hf]
    omega

/-- The quantifier may be over a function type, and inside the goal rather than in front of it:
here `g` ranges over `ZFNat × ZFNat → ZFNat` and comes back as `ℕ × ℕ → ℕ`. -/
example (f : ZFNat → ZFNat → ZFNat) :
    ∃ g : ZFNat × ZFNat → ZFNat, ∀ a b, f a b = g (a, b) := by
  transfer ZFNat → ℕ =>
    exact ⟨fun p => f p.1 p.2, fun a b => rfl⟩

/-- Strong induction on `ZFNat`, imported from `ℕ` rather than proved again. -/
example (P : ZFNat → Prop) (ih : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  transfer ZFNat → ℕ =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih' => exact ih n ih'

/-- The least number principle, from `Nat.find`. -/
example (P : ZFNat → Prop) (h : ∃ n, P n) : ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  transfer ZFNat → ℕ =>
    classical
    obtain ⟨n, hn⟩ := h
    exact ⟨Nat.find ⟨n, hn⟩, Nat.find_spec _, fun k hk => Nat.find_le hk⟩

/-! ## Arithmetic imported from mathlib -/

/-- One of two consecutive integers is even. -/
example (a : ZFInt) : 2 ∣ a * (a + 1) := by
  transfer ZFInt → ℤ =>
    exact Int.two_dvd_mul_add_one a

/-- `ZFRat` is archimedean, because `ℚ` is. `n` ranges over `ℕ`, a type the transfer leaves
alone, and the cast `(n : ZFRat)` becomes the cast `(n : ℚ)`. -/
example (x : ZFRat) : ∃ n : ℕ, x < n := by
  transfer ZFRat → ℚ =>
    exact exists_nat_gt x

/-- `ZFRat` is densely ordered, because `ℚ` is. -/
example (x y : ZFRat) (h : x < y) : ∃ z : ZFRat, x < z ∧ z < y := by
  transfer ZFRat → ℚ =>
    exact ⟨(x + y) / 2, by constructor <;> linarith⟩

/-! ## Booleans

`ZFBool` has two readings: as `Bool`, the registered one, and — classically — as `Prop`.
-/

/-! ### `ZFBool` read as `Bool` -/

/-- De Morgan on `ZFBool`, imported rather than proved again. -/
example (p q : ZFBool) : (p ⋀ q).not = p.not ⋁ q.not := by
  transfer ZFBool → Bool =>
    exact Bool.not_and p q

/-- `ZFBool` has two elements, because `Bool` has. -/
example (p : ZFBool) : p = ⊤ ∨ p = ⊥ := by
  transfer ZFBool → Bool =>
    cases p <;> simp

/-! ### `ZFBool` read as `Prop`

Classically `Bool` and `Prop` are the same type, so `ZFBool` is `Prop` as well: `equivProp p` is
the proposition that `p` is `⊤`, and the connectives of `ZFBool` become those of `Prop`. `Bool` is
the target `TransferEquiv` registers for `ZFBool`, so this reading is asked for by naming the
equivalence. -/

/-- `p ⋁ p.not = ⊤` is excluded middle, which is where the classical equivalence is paid for. -/
example (p : ZFBool) : p ⋁ p.not = ⊤ := by
  transfer ZFBool → Prop using ZFBool.equivProp =>
    exact em p

/-- A predicate over `ZFBool` becomes a predicate over propositions, and `⊤` becomes `True`. -/
example (P : ZFBool → Prop) (h : ∀ p, P p) : P ⊤ := by
  transfer ZFBool → Prop using ZFBool.equivProp =>
    exact h True

/-! ## The tactic itself -/

/-- The equivalence may be named instead of the two types; the direction is read off its type. -/
example (n m : ZFNat) : n * m = m * n := by
  transfer ZFNat.ringEquivNat =>
    rw [Nat.mul_comm]

/-- Or given explicitly, next to the types. -/
example (a b : ZFInt) : a * b = b * a := by
  transfer ZFInt → ℤ using ZFInt.equivInt =>
    ring

/-- The block does not have to close the goal: what it leaves is a goal about `Bool`, and closing
it later closes the goal about `ZFBool`. -/
example (p q : ZFBool) : p ⋀ q = q ⋀ p := by
  transfer ZFBool → Bool =>
    skip
  exact Bool.and_comm p q
