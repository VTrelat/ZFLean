/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import ZFLean.Naturals
import ZFLean.TransferAlgebra
import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Group.Defs

/-! # ZFC Integers

This file provides a construction of the integers in ZFC based on the construction of natural
numbers. It follows the usual construction of integers as equivalence classes of pairs of natural
numbers.

The theory also comes with usual theorems and arithmetic operations on integers and wraps everything
in a commutative ring structure.

Finally, we show that the `ZFInt` type is in canonical bijection with the type of elements
contained in `ZFSet.Int`. The bijection is built directly from the projection functions
`ZFInt.into` and `ZFInt.outof` — no Schröder–Bernstein, no `Classical.choice` over a non-empty
set of bijections — so the induced order on `{x // x ∈ ZFSet.Int}` is well-defined and concrete
inequalities like `0 < 1` are provable.
-/

public section

namespace ZFSet

section Integers

protected abbrev zrel (a b : ZFNat × ZFNat) : Prop := a.1 + b.2 = a.2 + b.1

protected def zrel_eq : Equivalence ZFSet.zrel where
  refl := fun _ => add_comm _ _
  symm := by
    unfold ZFSet.zrel
    intro x y h
    rw [add_comm, add_comm y.2]
    symm
    assumption
  trans := by
    unfold ZFSet.zrel
    intro x y z hxy hyz
    have : x.1 + y.2 + y.1 + z.2 = x.2 + y.1 + y.2 + z.1 := by
      rw [hxy, ← ZFNat.add_assoc, hyz, ZFNat.add_assoc _ _ _]
    rw [add_assoc x.1, add_comm _ (y.2 + y.1), add_assoc, add_assoc x.2, add_comm _ (y.1 + y.2),
      add_comm y.1, ← add_assoc (y.2 + y.1)] at this
    apply add_left_cancel (a := y.2 + y.1)
    simpa only [add_assoc]

protected instance instSetoidZFNatZFNat : Setoid (ZFNat × ZFNat) where
  r := ZFSet.zrel
  iseqv := ZFSet.zrel_eq

abbrev ZFInt := Quotient ZFSet.instSetoidZFNatZFNat

namespace ZFInt

@[expose] def mk : ZFNat × ZFNat → ZFInt := Quotient.mk''

@[simp]
theorem mk_eq (x : ZFNat × ZFNat) : @Eq ZFInt ⟦x⟧ (mk x) := rfl

@[simp]
theorem mk_out : ∀ x : ZFInt, mk x.out = x := Quotient.out_eq

theorem eq {x y : ZFNat × ZFNat} : mk x = mk y ↔ ZFSet.zrel x y := Quotient.eq

theorem sound {x y : ZFNat × ZFNat} (h : ZFSet.zrel x y) : mk x = mk y := Quotient.sound h

theorem exact {x y : ZFNat × ZFNat} : mk x = mk y → ZFSet.zrel x y := Quotient.exact

abbrev zero : ZFInt := mk (0, 0)
abbrev one : ZFInt := mk (1, 0) -- (0,1) works too

protected instance : Zero ZFInt := ⟨zero⟩
protected instance : One ZFInt := ⟨one⟩

theorem zero_eq : (0 : ZFInt) = mk (0, 0) := rfl
theorem one_eq : (1 : ZFInt) = mk (1, 0) := rfl

theorem one_ne_zero : (1 : ZFInt) ≠ 0 := by
  rw [zero_eq, one_eq]
  rintro h
  rw [ZFInt.eq, ZFSet.zrel] at h
  simp only [add_zero] at h
  unfold_projs at h
  injection h with h
  rw [ZFSet.ext_iff] at h
  simp only [mem_insert_iff, or_iff_right_iff_imp, forall_eq] at h
  nomatch h

theorem mk_eq_zero_iff {n m} : ZFInt.mk (n,m) = 0 ↔ n = m := by
  constructor
  · intro h
    rw [ZFInt.zero_eq, ZFInt.eq, ZFSet.zrel] at h
    exact ZFNat.add_right_cancel.mp h
  · rintro rfl
    exact ZFInt.sound rfl

open ZFNat in
noncomputable abbrev add (n m : ZFInt) : ZFInt :=
  Quotient.liftOn₂ n m (fun ⟨a, b⟩ ⟨c, d⟩ => mk (a + c, b + d)) fun x y x' y' hx hy => sound (by
    have h1 : x.1 + x'.2 = x.2 + x'.1 := hx
    have h2 : y.1 + y'.2 = y.2 + y'.1 := hy
    simp only [ZFSet.zrel]
    have : x.1 + x'.2 + y.1 + y'.2 = x.2 + x'.1 + y.2 + y'.1 := by
      rw [h1, ← add_assoc, h2, add_assoc]
    conv_lhs => rw [add_assoc, ← add_assoc, ← add_assoc, ZFNat.add_comm y.1, add_assoc, add_assoc,
      ← add_assoc, ZFNat.add_comm y'.2, add_assoc, this]
    conv_rhs => rw [add_assoc]; lhs; rw [← add_assoc]; rhs; rw [add_comm]
    rw [add_assoc])

protected noncomputable instance : Add ZFInt := ⟨ZFInt.add⟩
theorem add_eq (n m : ZFNat × ZFNat) : mk n + mk m = mk (n.1 + m.1, n.2 + m.2) := rfl

theorem add_assoc (n m k : ZFInt) : n + (m + k) = n + m + k := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  induction k using Quotient.ind
  simp_rw [mk_eq, ZFInt.add_eq, ZFNat.add_assoc]

theorem add_comm (n m : ZFInt) : n + m = m + n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  simp_rw [mk_eq, ZFInt.add_eq, ZFNat.add_comm]

lemma add_left_comm (n m k : ZFInt) : n + (m + k) = m + (n + k) := by
  rw [add_assoc, add_assoc, add_comm n]

lemma add_right_comm (n m k : ZFInt) : (n + m) + k = (n + k) + m := by
  rw [← add_assoc, add_comm m, add_assoc]

@[simp]
theorem add_zero {x : ZFInt} : x + 0 = x := by
  induction x using Quotient.ind
  simp_rw [mk_eq, zero_eq, ZFInt.add_eq, ZFNat.add_zero]

@[simp]
theorem zero_add {x : ZFInt} : 0 + x = x := by
  rw [add_comm, add_zero]

protected abbrev neg (n : ZFInt) : ZFInt :=
  Quotient.liftOn n (fun x => mk (x.2, x.1)) fun x y h => sound (ZFSet.zrel_eq.symm (by
    simp only [ZFSet.zrel]
    rw [ZFNat.add_comm, ZFNat.add_comm y.1, ← ZFSet.zrel]
    assumption))
protected instance : Neg ZFInt := ⟨ZFInt.neg⟩
theorem neg_eq (n : ZFNat × ZFNat) : -mk n = mk (n.2, n.1) := rfl

@[simp]
theorem neg_neg (n : ZFInt) : -(-n) = n := by
  induction n using Quotient.ind
  rw [mk_eq, neg_eq, neg_eq]

@[simp]
theorem neg_zero : -(0 : ZFInt) = 0 := by
  rw [zero_eq, neg_eq]

theorem neg_inj {a b : ZFInt} : -a = -b ↔ a = b :=
  ⟨fun h => by rw [← neg_neg a, ← neg_neg b, h], congrArg _⟩

@[simp]
theorem neg_eq_zero {a : ZFInt} : -a = 0 ↔ a = 0 := ZFInt.neg_inj (b := 0)

theorem neg_ne_zero {a : ZFInt} : -a ≠ 0 ↔ a ≠ 0 := not_congr neg_eq_zero

theorem add_left_neg {a : ZFInt} : -a + a = 0 := by
  induction a using Quotient.ind
  apply sound
  rw [ZFNat.add_comm]

theorem add_right_neg (a : ZFInt) : a + -a = 0 := by
  rw [add_comm]
  exact add_left_neg

theorem neg_eq_of_add_eq_zero {a b : ZFInt} (h : a + b = 0) : -a = b := by
  rw [← @add_zero (-a), ← h, add_assoc, add_left_neg, zero_add]

theorem eq_neg_of_eq_neg {a b : ZFInt} (h : a = -b) : b = -a := by
  rw [h, neg_neg]

theorem eq_neg_comm {a b : ZFInt} : a = -b ↔ b = -a := ⟨eq_neg_of_eq_neg, eq_neg_of_eq_neg⟩

theorem neg_eq_comm {a b : ZFInt} : -a = b ↔ -b = a := by
  rw [eq_comm, eq_neg_comm, eq_comm]

theorem neg_add_cancel_left (a b : ZFInt) : -a + (a + b) = b := by
  rw [add_assoc, add_left_neg, zero_add]

theorem add_neg_cancel_left (a b : ZFInt) : a + (-a + b) = b := by
  rw [add_assoc, add_right_neg, zero_add]

theorem add_neg_cancel_right (a b : ZFInt) : a + b + -b = a := by
  rw [← add_assoc, add_right_neg, add_zero]

theorem neg_add_cancel_right (a b : ZFInt) : a + -b + b = a := by
  rw [← add_assoc, add_left_neg, add_zero]

theorem add_left_cancel {a b c : ZFInt} (h : a + b = a + c) : b = c := by
  have h₁ : -a + (a + b) = -a + (a + c) := by rw [h]
  simp only [add_assoc, add_left_neg, zero_add] at h₁
  exact h₁

@[simp]
theorem neg_add {a b : ZFInt} : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_right_neg, add_comm a, add_assoc, ← add_assoc b, add_right_neg, add_zero, add_right_neg]

noncomputable abbrev sub (n m : ZFInt) : ZFInt := n + -m
protected noncomputable instance : Sub ZFInt := ⟨ZFInt.sub⟩
theorem sub_eq (n m : ZFNat × ZFNat) : mk n - mk m = mk (n.1 + m.2, n.2 + m.1) := rfl

theorem sub_eq_add_neg {a b : ZFInt} : a - b = a + -b := rfl

theorem add_neg_one (i : ZFInt) : i + -1 = i - 1 := rfl

@[simp]
theorem sub_self (a : ZFInt) : a - a = 0 := by rw [sub_eq_add_neg, add_right_neg]

@[simp]
theorem sub_zero (a : ZFInt) : a - 0 = a := by simp [sub_eq_add_neg]

@[simp]
theorem zero_sub (a : ZFInt) : 0 - a = -a := by simp [sub_eq_add_neg]

theorem sub_eq_zero_of_eq {a b : ZFInt} (h : a = b) : a - b = 0 := by rw [h, sub_self]

theorem eq_of_sub_eq_zero {a b : ZFInt} (h : a - b = 0) : a = b := by
  have : 0 + b = b := by rw [zero_add]
  have : a - b + b = b := by rwa [h]
  rwa [sub_eq_add_neg, neg_add_cancel_right] at this

theorem sub_eq_zero {a b : ZFInt} : a - b = 0 ↔ a = b := ⟨eq_of_sub_eq_zero, sub_eq_zero_of_eq⟩

theorem sub_sub (a b c : ZFInt) : a - b - c = a - (b + c) := by
  simp [sub_eq_add_neg, add_assoc]

theorem neg_sub (a b : ZFInt) : -(a - b) = b - a := by
  simp [sub_eq_add_neg, add_comm]

theorem sub_sub_self (a b : ZFInt) : a - (a - b) = b := by
  simp [sub_eq_add_neg, add_assoc, add_right_neg]

@[simp]
theorem sub_neg (a b : ZFInt) : a - -b = a + b := by simp [sub_eq_add_neg]

@[simp]
theorem sub_add_cancel (a b : ZFInt) : a - b + b = a := neg_add_cancel_right a b

@[simp]
theorem add_sub_cancel (a b : ZFInt) : a + b - b = a := add_neg_cancel_right a b

theorem add_sub_assoc (a b c : ZFInt) : a + b - c = a + (b - c) := by
  rw [sub_eq_add_neg, ← add_assoc, ← sub_eq_add_neg]

theorem sub_left_cancel (a b c : ZFInt) : a - c = b - c → a = b := by
  intro h
  rwa [← sub_eq_zero, sub_sub, sub_eq_zero, ← add_sub_assoc, add_comm, add_sub_cancel] at h

theorem sub_right_cancel (a b c : ZFInt) : c - a = c - b → a = b := by
  rw [← neg_sub a, ← neg_sub b, neg_inj]
  apply sub_left_cancel

theorem add_eq_sub_iff {a b c : ZFInt} : a + b = c ↔ a = c - b where
  mp := fun h => by rw [← h, add_sub_cancel]
  mpr := fun h => by rw [h, sub_add_cancel]

noncomputable abbrev nsmul : ℕ → ZFInt → ZFInt
  | 0, _ => 0
  | n+1, m => m + nsmul n m

noncomputable abbrev zsmul (n : ℤ) (x : ZFInt) : ZFInt :=
  match n with
  | .ofNat n => nsmul n x
  | .negSucc n => -nsmul (n+1) x

theorem mul_wf {a b c d s t u v : ZFNat}
  (h₁ : ZFSet.zrel (a, b) (s, t)) (h₂ : ZFSet.zrel (c, d) (u, v)) :
  ZFSet.zrel (a * c + b * d, a * d + b * c) (s * u + t * v, s * v + t * u) := by
  dsimp [ZFSet.zrel] at *
  suffices h₃ : t * c + a * c + b * d + s * v + t * u = a * d + b * c + s * u + t * v + t * c by
    simp_rw [ZFNat.add_comm _ (t*c), ← ZFNat.add_assoc (t*c)] at h₃
    apply ZFNat.add_left_cancel.mp at h₃
    simp_rw [ZFNat.add_assoc, h₃]
  conv in t*c + a*c => rw [← right_distrib, ZFNat.add_comm, h₁, right_distrib]
  conv in _ + t*v + t*c => rw [← ZFNat.add_assoc, ← left_distrib, ZFNat.add_comm v c, h₂,
    left_distrib, ZFNat.add_assoc]
  apply ZFNat.add_right_cancel.mpr
  conv_rhs =>
    rw [ZFNat.add_comm, ZFNat.add_assoc, ZFNat.add_assoc, ← right_distrib, ZFNat.add_comm t a, h₁,
      right_distrib]
    rw [ZFNat.add_comm (b * d + s * d), ZFNat.add_assoc, ← ZFNat.add_assoc,  ← left_distrib s, ← h₂,
      left_distrib]
  ac_rfl

noncomputable abbrev mul (n m : ZFInt) : ZFInt :=
  Quotient.liftOn₂ n m
    (fun ⟨a, b⟩ ⟨c, d⟩ => mk (a * c + b * d, a * d + b * c)) fun _ _ _ _ => (sound <| mul_wf · ·)

noncomputable instance : Mul ZFInt := ⟨ZFInt.mul⟩
theorem mul_eq (n m : ZFNat × ZFNat) :
  mk n * mk m = mk (n.1 * m.1 + n.2 * m.2, n.1 * m.2 + n.2 * m.1) := rfl

theorem mul_comm (n m : ZFInt) : n * m = m * n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  apply sound
  rw [ZFSet.zrel]
  ac_rfl

theorem left_distrib (a b c : ZFInt) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  rename_i a b c
  let ⟨a₁, a₂⟩ := a
  let ⟨b₁, b₂⟩ := b
  let ⟨c₁, c₂⟩ := c
  apply sound
  simp_rw [ZFNat.left_distrib, ZFSet.zrel]
  ac_rfl

theorem right_distrib (a b c : ZFInt) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm, mul_comm b c]

@[simp]
theorem zero_mul (a : ZFInt) : 0 * a = 0 := by
  induction a using Quotient.ind
  apply sound
  simp_rw [ZFNat.zero_mul]

@[simp]
theorem mul_zero (a : ZFInt) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem mul_assoc (a b c : ZFInt) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply sound
  simp_rw [ZFSet.zrel, ZFNat.left_distrib, ZFNat.right_distrib]
  ac_rfl

@[simp]
theorem one_mul (a : ZFInt) : 1 * a = a := by
  induction a using Quotient.ind
  apply sound
  simp_rw [ZFNat.one_mul, ZFNat.zero_mul, ZFNat.add_zero]
  apply ZFSet.zrel_eq.refl

@[simp]
theorem mul_one (a : ZFInt) : a * 1 = a := by
  rw [mul_comm, one_mul]

noncomputable instance : CommRing ZFInt where
  zero := 0
  one := 1
  add := add
  add_assoc _ _ _ := by rw [add_assoc]
  zero_add _ := zero_add
  add_zero _ := add_zero
  nsmul := ZFSet.ZFInt.nsmul
  nsmul_zero _ := rfl
  nsmul_succ _ _ := add_comm _ _
  add_comm := add_comm
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  zsmul := ZFSet.ZFInt.zsmul
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := add_comm _ _
  zsmul_neg' _ _ := rfl
  neg_add_cancel _ := add_left_neg

section Inequalities

instance int_lt : LT ZFInt where
  lt x y := Quotient.liftOn₂ x y
    (fun ⟨a, b⟩ ⟨c, d⟩ => a + d < b + c) fun ⟨a, b⟩ ⟨c, d⟩ ⟨s, t⟩ ⟨u, v⟩ h₁ h₂ => by
      replace h₁ : a + t = b + s := h₁
      replace h₂ : c + v = d + u := h₂
      simp only [eq_iff_iff]
      apply Iff.intro
      · intro lt
        rw [← ZFNat.add_lt_add_iff_right (k := t)] at lt
        conv_lhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm, ← ZFNat.add_assoc,
          ZFNat.add_comm t, h₁, ZFNat.add_comm b, ZFNat.add_assoc]
        conv_rhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm]
        rw [ZFNat.add_lt_add_iff_right, ← ZFNat.add_lt_add_iff_right (k := u)] at lt
        conv_lhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm, ← ZFNat.add_assoc,
          ZFNat.add_comm u, ← h₂, ZFNat.add_assoc, ZFNat.add_comm, ZFNat.add_assoc]
        conv_rhs at lt => rw [ZFNat.add_comm, ZFNat.add_comm c, ZFNat.add_assoc]
        rwa [ZFNat.add_lt_add_iff_right, ZFNat.add_comm, ZFNat.add_comm u] at lt
      · intro lt
        rw [← ZFNat.add_lt_add_iff_right (k := b)] at lt
        conv_lhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm, ← ZFNat.add_assoc, ← h₁,
          ZFNat.add_assoc]
        conv_rhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm]
        rw [ZFNat.add_lt_add_iff_right, ← ZFNat.add_lt_add_iff_right (k := c)] at lt
        conv_lhs at lt => rw [ZFNat.add_comm, ZFNat.add_assoc, h₂, ZFNat.add_comm, ZFNat.add_assoc]
        conv_rhs at lt => rw [ZFNat.add_comm, ZFNat.add_comm u, ZFNat.add_assoc]
        rwa [ZFNat.add_lt_add_iff_right, ZFNat.add_comm c] at lt

instance int_le : LE ZFInt where
  le x y := x < y ∨ x = y

theorem lt_succ {n : ZFInt} : n < n + 1 := by
  induction n using Quotient.ind with
  | _ n =>
    obtain ⟨n, m⟩ := n
    rw [ZFInt.mk_eq, ZFInt.one_eq, ZFInt.add_eq]
    dsimp
    rw [ZFNat.add_zero]
    change n+m < m+(n+1)
    rw [ZFNat.add_comm, ZFNat.add_lt_add_iff_left, ZFNat.add_one_eq_succ]
    exact ZFNat.lt_succ

theorem lt_trans {a b c : ZFInt} : a < b → b < c → a < c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  rename_i a b c
  let ⟨a₁, a₂⟩ := a
  let ⟨b₁, b₂⟩ := b
  let ⟨c₁, c₂⟩ := c
  intros h₁ h₂
  let this := ZFNat.add_lt_trans h₁ h₂
  conv at this =>
    conv => lhs; rw [← ZFNat.add_assoc, ZFNat.add_comm b₂, ZFNat.add_comm b₁, ZFNat.add_assoc,
      ZFNat.add_assoc]
    conv => rhs; rw [← ZFNat.add_assoc, ZFNat.add_comm b₁, ZFNat.add_comm b₂, ← ZFNat.add_assoc,
      ZFNat.add_comm b₂, ZFNat.add_assoc, ZFNat.add_assoc]
    rw [ZFNat.add_lt_add_iff_right (k := b₂), ZFNat.add_lt_add_iff_right (k := b₁)]
  assumption

theorem lt_irrefl {a : ZFInt} : ¬ a < a := by
  induction a using Quotient.ind with
  | _ a =>
    let ⟨a₁, a₂⟩ := a
    intro h
    replace h : a₁ + a₂ < a₂ + a₁ := h
    rw [ZFNat.add_comm] at h
    nomatch ZFNat.lt_irrefl h

theorem lt_zero_iff {n m : ZFNat} : m < n ↔ 0 < ZFInt.mk (n,m) := by
  constructor
  · intro h
    induction n using ZFNat.induction generalizing m with
    | zero =>
      rw [ZFInt.zero_eq]
      change 0 + m < 0 + 0
      exact ZFNat.add_lt_add_left h 0
    | succ n ih =>
      rw [ZFInt.zero_eq]
      change 0 + m < 0 + n.succ
      exact ZFNat.add_lt_add_left h 0
  · intro h
    rw [ZFInt.zero_eq] at h
    change 0 + m < 0 + n at h
    exact ZFNat.add_lt_add_iff_left.mp h

theorem neg_one_lt_zero : (-1 : ZFInt) < 0 := add_left_neg ▸ lt_succ (n := (-1))
theorem zero_lt_one : (0 : ZFInt) < 1 := ZFInt.zero_add (x:=1) ▸ lt_succ

theorem le_trans {a b c : ZFInt} : a ≤ b → b ≤ c → a ≤ c := by
  intro h₁ h₂
  rcases h₁ with h₁ | rfl
  · rcases h₂ with h₂ | rfl
    · left
      exact lt_trans h₁ h₂
    · left; assumption
  · assumption

theorem le_antisymm {a b : ZFInt} : a ≤ b → b ≤ a → a = b := by
  intro h₁ h₂
  rcases h₁ with h₁ | rfl
  · rcases h₂ with h₂ | rfl
    · nomatch lt_irrefl <| lt_trans h₁ h₂
    · rfl
  · rfl

theorem le_total {a b : ZFInt} : a ≤ b ∨ b ≤ a := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i a b
  let ⟨a₁, a₂⟩ := a
  let ⟨b₁, b₂⟩ := b
  rcases @ZFNat.le_total (a₁ + b₂) (a₂ + b₁) with (_ | _) | (h | h)
  · left; left; assumption
  · left; right; apply sound; assumption
  · right; left; rw [ZFNat.add_comm a₂, ZFNat.add_comm a₁] at h; assumption
  · right; right; apply sound; rw [ZFNat.add_comm a₂, ZFNat.add_comm a₁] at h; assumption

theorem lt_iff_le_not_ge {x y : ZFInt} : x < y ↔ x ≤ y ∧ ¬y ≤ x := by
  apply Iff.intro
  · intro
    apply And.intro
    · left
      assumption
    · rintro (_ | rfl)
      · nomatch lt_irrefl (lt_trans ‹_› ‹_›)
      · nomatch lt_irrefl ‹_›
  · rintro ⟨h | rfl, h'⟩
    · assumption
    · simp only [LE.le, or_true] at h'
      contradiction

theorem lt_neg_iff {a b : ZFInt} : a < b ↔ -b < -a := by
  constructor <;>
  (
    intro le
    induction a using Quotient.ind
    induction b using Quotient.ind
    rename_i a b
    let ⟨a₁, a₂⟩ := a
    let ⟨b₁, b₂⟩ := b
    rw [ZFInt.mk_eq, ZFInt.mk_eq] at le ⊢
  )
  · change a₁ + b₂ < a₂ + b₁ at le
    change b₂ + a₁ < b₁ + a₂
    rwa [ZFNat.add_comm b₂, ZFNat.add_comm b₁]
  · change b₂ + a₁ < b₁ + a₂ at le
    change a₁ + b₂ < a₂ + b₁
    rwa [ZFNat.add_comm a₂, ZFNat.add_comm a₁]

theorem le_neg_iff {a b : ZFInt} : a ≤ b ↔ -b ≤ -a := by
  constructor <;>
  (
    intro le
    induction a using Quotient.ind
    induction b using Quotient.ind
    rename_i a b
    let ⟨a₁, a₂⟩ := a
    let ⟨b₁, b₂⟩ := b
    rw [ZFInt.mk_eq, ZFInt.mk_eq] at le ⊢
  )
  · rcases le with le | le
    · left
      exact lt_neg_iff.mp le
    · rw [eq, ZFSet.zrel] at le
      right
      rwa [neg_eq, neg_eq, eq, ZFSet.zrel, ZFNat.add_comm b₂, ZFNat.add_comm b₁]
  · rcases le with le | le
    · left
      exact lt_neg_iff.mpr le
    · rw [neg_eq, neg_eq, eq, ZFSet.zrel] at le
      right
      rwa [eq, ZFSet.zrel, ZFNat.add_comm a₁, ZFNat.add_comm a₂]

noncomputable instance : LinearOrder ZFInt where
  le := int_le.le
  le_refl x := Or.inr rfl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total _ _ := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable ((· ≤ ·) _ _)
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

noncomputable instance : AddCommGroup ZFInt where
  add := add
  add_assoc := (add_assoc · · · |>.symm)
  zero := zero
  zero_add := @zero_add
  add_zero := @add_zero
  nsmul := nsmul
  nsmul_succ x y := add_comm y (nsmul x y)
  neg := ZFInt.neg
  zsmul := zsmul
  zsmul_succ' x y := add_comm y (nsmul x y)
  neg_add_cancel := @add_left_neg
  add_comm := @add_comm

instance : PartialOrder ZFInt where
  le := int_le.le
  le_refl := le_refl
  le_trans := @le_trans
  lt_iff_le_not_ge := @lt_iff_le_not_ge
  le_antisymm := @le_antisymm

instance : IsOrderedAddMonoid ZFInt where
  add_le_add_left x y h z := by
    induction x using Quotient.ind
    induction y using Quotient.ind
    induction z using Quotient.ind
    rename_i x y z
    let ⟨x₁, x₂⟩ := x
    let ⟨y₁, y₂⟩ := y
    let ⟨z₁, z₂⟩ := z
    simp_rw [mk_eq] at h ⊢
    rcases h with h | h
    · change x₁ + y₂ < x₂ + y₁ at h
      simp_rw [add_eq]
      left
      change (x₁ + z₁) + (y₂ + z₂) < (x₂ + z₂) + (y₁ + z₁)
      ac_change (x₁ + y₂) + (z₁ + z₂) <  (x₂ + y₁) + (z₁ + z₂)
      rwa [ZFNat.add_lt_add_iff_right]
    · rw [eq, ZFSet.zrel] at h
      dsimp at h
      right
      rw [add_eq, add_eq, eq, ZFSet.zrel]
      dsimp
      ac_change (x₁ + y₂) + (z₁ + z₂) =  (x₂ + y₁) + (z₁ + z₂)
      rw [h]

end Inequalities

section Induction

lemma ind {P : ZFNat → ZFNat → Prop} (n m : ZFNat) (zero : P 0 0)
  (succ_l : ∀ n m, P n m → P (n + 1) m) (succ_r : ∀ n m, P n m → P n (m + 1)) : P n m := by
  induction n using ZFNat.induction with
  | zero =>
    induction m using ZFNat.induction with
    | zero => exact zero
    | succ m ih =>
      rw [←ZFNat.add_one_eq_succ]
      exact succ_r 0 m ih
  | succ n ih =>
    rw [←ZFNat.add_one_eq_succ]
    exact succ_l n m ih

lemma induction_pos {P : ZFInt → Prop} (n : ZFInt) (n_pos : 0 ≤ n)
  (zero : P 0) (succ : ∀ k, P k → P (k + 1)) : P n := by
  induction n using Quotient.ind
  rename_i n
  obtain ⟨n, m⟩ := n
  rcases lt_trichotomy n m with h | rfl | h
  · exfalso
    rw [ZFInt.lt_zero_iff] at h
    rcases n_pos with n_pos | eq
    · rw [ZFInt.zero_eq] at h n_pos
      change 0 + n < 0 + m at h
      change 0 + m < 0 + n at n_pos
      rw [ZFNat.zero_add, ZFNat.zero_add] at h n_pos
      nomatch ZFNat.lt_irrefl <| ZFNat.lt_trans h n_pos
    · rw [ZFInt.mk_eq] at eq
      rcases ZFInt.mk_eq_zero_iff.mp eq.symm with rfl
      rw [eq] at h
      change n + n < n + n at h
      nomatch ZFNat.lt_irrefl h
  · rcases n_pos with n_pos | eq
    · rw [ZFInt.zero_eq] at n_pos
      change 0 + n < 0 + n at n_pos
      nomatch ZFNat.lt_irrefl n_pos
    · rwa [←eq]
  · let k := n - m
    have : n = k + m := by
      apply ZFNat.eq_add_of_sub_eq _ rfl
      left
      exact h
    rw [this]
    induction k using ZFNat.induction with
    | zero =>
      rw [ZFInt.zero_eq] at zero
      rwa [ZFNat.zero_add, ZFInt.mk_eq, ZFInt.eq (x := (m,m)) (y := (0,0)) |>.mpr rfl]
    | succ k ih =>
      rw [ZFNat.add_comm] at ih
      rw [←ZFNat.add_one_eq_succ, ZFNat.add_comm, ZFNat.add_assoc]
      specialize succ <| ZFInt.mk (m+k,m)
      rw [ZFInt.one_eq, ZFInt.add_eq] at succ
      dsimp at succ
      rw [ZFNat.add_zero, ←ZFInt.mk_eq] at succ
      exact succ ih

lemma induction_neg {P : ZFInt → Prop} (n : ZFInt) (n_neg : n ≤ 0)
  (zero : P 0) (succ : ∀ k, P k → P (k - 1)) : P n := by
  have  : 0 ≤ -n := by rwa [← ZFInt.neg_zero, ZFInt.le_neg_iff, neg_neg n, neg_neg 0]
  letI P' n := P (-n)
  suffices P' (-n) by
    unfold P' at this
    rwa [ZFInt.neg_neg] at this
  have succ' : ∀ k, P' k → P' (k + 1) := by
    intro k hk
    unfold P' at hk ⊢
    rw [ZFInt.neg_add]
    exact succ _ hk
  exact induction_pos (P := P') (-n) this zero succ'

@[induction_eliminator]
theorem induction {P : ZFInt → Prop} (n : ZFInt)
  (zero : P 0) (pos : ∀ k, P k → P (k + 1)) (neg : ∀ k, P k → P (k - 1)) : P n := by
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact induction_neg n (Or.inl h) zero neg
  · exact zero
  · exact induction_pos n (Or.inl h) zero pos

@[cases_eliminator]
theorem sign_cases {P : ZFInt → Prop} (n : ZFInt)
  (zero : P 0) (neg : n < 0 → P n) (pos : 0 < n → P n) : P n := by
  induction n with
  | zero => exact zero
  | pos k ih =>
    rcases lt_trichotomy (k+1) 0 with h | h | h
    · exact neg h
    · rwa [h]
    · exact pos h
  | neg k ih =>
    rcases lt_trichotomy (k-1) 0 with h | h | h
    · exact neg h
    · rwa [h]
    · exact pos h

@[cases_eliminator]
theorem cases {P : ZFInt → Prop} (n : ZFInt) (pos : 0 ≤ n → P n) (neg : n < 0 → P n) : P n := by
  induction n with
  | zero => exact pos (Or.inr rfl)
  | pos n ih =>
    generalize h : n + 1 = m at *
    cases m using sign_cases with
    | zero => exact pos (Or.inr rfl)
    | neg h => exact neg h
    | pos h => exact pos (Or.inl h)
  | neg n ih =>
    generalize h : n - 1 = m at *
    cases m using sign_cases with
    | zero => exact pos (Or.inr rfl)
    | neg h => exact neg h
    | pos h => exact pos (Or.inl h)

end Induction

theorem add_eq_add_sub_eq_sub {a b c d : ZFNat} : a + b = c + d → a - c = d - b := by
  intro h
  have : a = c + d - b := ZFNat.sub_eq_of_eq_add h.symm |>.symm
  subst this
  rw [←ZFNat.sub_add_distrib, ZFNat.add_comm b c, ZFNat.add_sub_add_left c d b]

theorem le_of_lt_succ (n m : ZFInt) : n < m + 1 → n ≤ m := by
  intro h
  induction n using Quotient.ind
  induction m using Quotient.ind
  rename_i n m
  obtain ⟨a, b⟩ := n
  obtain ⟨c, d⟩ := m
  simp_rw [mk_eq] at h ⊢
  rw [one_eq, add_eq, ZFNat.add_zero] at h
  change a + d < b + (c + 1) at h
  suffices a + d ≤ b + c by
    rcases this with h | h
    · left; exact h
    · right; exact sound h
  rwa [ZFNat.add_assoc, ZFNat.add_one_eq_succ, ←ZFNat.lt_le_iff] at h

theorem lt_succ_of_le (n m : ZFInt) : n ≤ m → n < m + 1 := by
  rintro (h | rfl)
  · trans n+1
    · exact lt_succ
    · exact (add_lt_add_iff_right 1).mpr h
  · exact lt_succ

theorem lt_succ_of_le_iff (n m : ZFInt) : n ≤ m ↔ n < m + 1 where
  mp := lt_succ_of_le n m
  mpr := le_of_lt_succ n m

theorem int_le.dest {n m : ZFInt} : n ≤ m → ∃ k, 0 ≤ k ∧ n + k = m := by
  intro h
  exists m - n
  and_intros
  · exact sub_nonneg_of_le h
  · exact _root_.add_sub_cancel n m

theorem mul_pos_pos_pos (a b : ZFInt) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i a b
  obtain ⟨c, d⟩ := b
  obtain ⟨a, b⟩ := a
  simp_rw [mk_eq, zero_eq] at ha hb ⊢
  rw [mul_eq]
  change 0 + d < 0 + c at hb
  change 0 + b < 0 + a at ha
  change 0 + (a * d + b * c) < 0 + (a * c + b * d)
  simp_rw [ZFNat.zero_add] at ha hb ⊢
  rw [ZFNat.sub_add_cancel (Or.inl hb) |>.symm, ZFNat.left_distrib, ZFNat.left_distrib,
    ZFNat.add_comm _ (b*d), ZFNat.add_assoc, ←ZFNat.right_distrib, ←ZFNat.add_assoc,
    ←ZFNat.right_distrib, ZFNat.add_comm, ZFNat.add_lt_add_iff_right, ZFNat.mul_comm b,
    ZFNat.mul_comm a]
  apply ZFNat.mul_lt_mono
  · exact ZFNat.pos_of_ne_zero (ZFNat.sub_ne_zero_of_lt hb).symm
  · exact ha

theorem neg_one_mul (a : ZFInt) : (-1 : ZFInt) * a = -a := by
  induction a using Quotient.ind
  rename_i a
  obtain ⟨a, b⟩ := a
  rw [mk_eq, one_eq, neg_eq, mul_eq, neg_eq]
  dsimp
  rw [ZFNat.zero_mul, ZFNat.zero_mul, ZFNat.one_mul, ZFNat.one_mul, ZFNat.zero_add, ZFNat.zero_add]

theorem neg_one_mul_neg_one : (-1 : ZFInt) * (-1) = 1 := by
  rw [one_eq, neg_eq, mul_eq, ZFNat.mul_zero, ZFNat.zero_mul, ZFNat.zero_add, ZFNat.zero_add,
    ZFNat.one_mul, ZFNat.one_mul]

theorem mul_neg_neg (a b : ZFInt) : a * b = -a * -b := by
  rw [←one_mul (a*b), ←neg_one_mul_neg_one, ←mul_assoc, mul_comm, mul_assoc, mul_comm, mul_assoc,
    mul_comm (-1), mul_assoc, mul_comm b, neg_one_mul, neg_one_mul]

theorem neg_mul_distrib (a b : ZFInt) : -(a * b) = -a * b := neg_mul_eq_neg_mul a b

theorem mul_neg_neg_pos (a b : ZFInt) (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  rw [mul_neg_neg]
  exact mul_pos_pos_pos _ _ (Left.neg_pos_iff.mpr ha) (Left.neg_pos_iff.mpr hb)

theorem neg_flip_lt (a : ZFInt) : a < 0 ↔ 0 < -a := Iff.symm Left.neg_pos_iff
theorem neg_flip_le (a : ZFInt) : a ≤ 0 ↔ 0 ≤ -a := Iff.symm neg_nonneg

theorem mul_neg_pos_neg (a b : ZFInt) (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  rw [neg_flip_lt, neg_mul_eq_neg_mul]
  exact mul_pos_pos_pos _ _ ((neg_flip_lt a).mp ha) hb

theorem mul_pos_neg_neg (a b : ZFInt) (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  rw [mul_comm, neg_flip_lt, neg_mul_eq_neg_mul]
  exact mul_pos_pos_pos _ _ ((neg_flip_lt b).mp hb) ha

theorem mul_nonneg_nonneg_nonneg (a b : ZFInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · left
    exact mul_pos_pos_pos a b ha hb
  · right
    rw [mul_zero]
  · right
    rw [zero_mul]
  · right
    rw [zero_mul]

theorem mul_nonpos_nonneg_nonpos (a b : ZFInt) (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  rw [neg_flip_le, neg_mul_eq_neg_mul]
  exact mul_nonneg_nonneg_nonneg _ _ (neg_nonneg.mpr ha) hb

theorem mul_nonneg_nonpos_nonpos (a b : ZFInt) (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  rw [mul_comm, neg_flip_le, neg_mul_eq_neg_mul]
  exact mul_nonneg_nonneg_nonneg _ _ (neg_nonneg.mpr hb) ha

theorem mul_nonpos_nonpos_nonneg (a b : ZFInt) (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  rw [mul_neg_neg]
  exact mul_nonneg_nonneg_nonneg _ _ (neg_nonneg.mpr ha) (neg_nonneg.mpr hb)

theorem mul_le_mul_left {n m : ZFInt} (k : ZFInt) (h : n ≤ m) (h' : 0 ≤ k) : k * n ≤ k * m := by
  obtain ⟨l, pos, hl⟩ := int_le.dest h
  have : k * n + k * l = k * m := by rw [←hl, left_distrib]
  rw [←this]
  apply le_add_of_nonneg_right
  exact mul_nonneg_nonneg_nonneg k l h' pos

theorem mul_lt_mul_of_pos_left {n m k : ZFInt} (h : n < m) (hk : k > 0) : k * n < k * m := by
  apply lt_of_lt_of_le (b := k*n+k)
  · exact lt_add_of_pos_right _ hk
  · conv =>
      enter [1,2]
      rw [←mul_one k]
    rw [←left_distrib]
    apply mul_le_mul_left k
    · exact (lt_succ_of_le_iff (n + 1) m).mpr <| (add_lt_add_iff_right 1).mpr h
    · exact le_of_lt hk

theorem pos_of_mul_pos {a b : ZFInt} (h : 0 < a * b) (ha : 0 < a) : 0 < b := by
  classical
  by_contra hb
  rw [not_lt_iff_eq_or_lt] at hb
  rcases hb with rfl | hb
  · rw [mul_zero] at h
    exact lt_irrefl h
  · rcases lt_trichotomy a b with h' | rfl | h'
    · nomatch lt_irrefl <| lt_trans (lt_trans ha h') hb
    · nomatch lt_irrefl <| lt_trans ha hb
    · nomatch lt_irrefl <| lt_trans h <| mul_pos_neg_neg a b ha hb

theorem mul_lt_mul_of_pos_right {n m k : ZFInt} (h : n < m) (hk : k > 0) : n * k < m * k := by
  rw [mul_comm n, mul_comm m]
  exact mul_lt_mul_of_pos_left h hk

theorem mul_pos_iff {a b : ZFInt} : 0 < a * b ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
  constructor
  · intro h
    cases a with
    | pos pos =>
      rcases pos with pos | rfl
      · left
        and_intros
        · exact pos
        · exact pos_of_mul_pos h pos
      · rw [zero_mul] at h
        nomatch lt_irrefl h
    | neg neg =>
      right
      and_intros
      · exact neg
      · rw [mul_neg_neg] at h
        rw [neg_flip_lt] at neg
        have := pos_of_mul_pos h neg
        rwa [←neg_flip_lt] at this
  · rintro (⟨l, r⟩ | ⟨l, r⟩)
    · exact mul_pos_pos_pos a b l r
    · exact mul_neg_neg_pos a b l r

theorem eq_le_iff {a b : ZFInt} : a = b ↔ a ≤ b ∧ b ≤ a := by
  constructor
  · rintro rfl
    exact ⟨le_refl _, le_refl _⟩
  · rintro ⟨h₁, h₂⟩
    rcases h₁ with h₁ | rfl <;> rcases h₂ with h₂ | h₂
    · nomatch lt_irrefl <| lt_trans h₁ h₂
    · exact h₂.symm
    · rfl
    · rfl

theorem mul_eq_zero_iff {a b : ZFInt} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    induction a using Quotient.ind
    induction b using Quotient.ind
    rename_i a b
    simp_rw [mk_eq, mul_eq, zero_eq, eq, ZFSet.zrel, ZFNat.add_zero] at h ⊢
    rcases lt_trichotomy b.1 b.2 with h' | eq | h'
    · have := ZFNat.add_eq_add_sub_eq_sub h.symm
      rw [←ZFNat.left_distrib_mul_sub, ←ZFNat.left_distrib_mul_sub] at this
      have b₁b₂_ne_0 : b.2 - b.1 ≠ 0 := by
        intro contr
        rw [ZFNat.sub_eq_zero_imp_le] at contr
        rcases contr with contr | eq
        · nomatch ZFNat.lt_irrefl <| ZFNat.lt_trans contr h'
        · rw [eq] at h'
          nomatch ZFNat.lt_irrefl h'
      left
      exact ZFNat.mul_right_cancel_iff b₁b₂_ne_0 |>.mp this
    · right; assumption
    · have := ZFNat.add_eq_add_sub_eq_sub h
      rw [←ZFNat.left_distrib_mul_sub, ←ZFNat.left_distrib_mul_sub] at this
      have b₁b₂_ne_0 : b.1 - b.2 ≠ 0 := by
        intro contr
        rw [ZFNat.sub_eq_zero_imp_le] at contr
        rcases contr with contr | eq
        · nomatch ZFNat.lt_irrefl <| ZFNat.lt_trans contr h'
        · rw [eq] at h'
          nomatch ZFNat.lt_irrefl h'
      left
      exact ZFNat.mul_right_cancel_iff b₁b₂_ne_0 |>.mp this
  · rintro (h | h)
    · rw [h, zero_mul]
    · rw [h, mul_zero]

theorem mul_eq_zero_of_ne_zero {a b : ZFInt} : a * b = 0 → a ≠ 0 → b = 0 := by
  intro h h'
  rw [mul_eq_zero_iff] at h
  exact Or.resolve_left h h'

theorem mul_left_cancel_iff {a b n : ZFInt} (h : n ≠ 0) : n * a = n * b ↔ a = b := by
  constructor
  · intro eq
    have : n*a - n*b = 0 := sub_eq_zero_of_eq eq
    rw [ZFInt.sub_eq_add_neg, mul_comm n b, neg_mul_distrib, mul_comm _ n, ←left_distrib,
      mul_eq_zero_iff] at this
    rcases this with rfl | this
    · nomatch h
    · exact eq_of_sub_eq_zero this
  · exact fun h => h ▸ rfl

theorem mul_right_cancel_iff {a b n : ZFInt} (h : n ≠ 0) : a * n = b * n ↔ a = b := by
  rw [mul_comm a n, mul_comm b n]
  exact mul_left_cancel_iff h

noncomputable instance : CommRing ZFInt where
  add := add
  add_assoc := (add_assoc · · · |>.symm)
  add_comm := add_comm
  zero_add _ := zero_add
  add_zero _ := add_zero
  nsmul := nsmul
  nsmul_succ x y := add_comm y (nsmul x y)
  left_distrib := left_distrib
  right_distrib := right_distrib
  zsmul := zsmul
  zsmul_succ' x y := add_comm y (nsmul x y)
  neg_add_cancel := @add_left_neg

instance : IsOrderedRing ZFInt where
  add_le_add_left _ _ h z := add_le_add_left h z
  zero_le_one := Or.inl zero_lt_one
  mul_le_mul_of_nonneg_left a b := fun _ _ ↦ (mul_le_mul_left a · b)
  mul_le_mul_of_nonneg_right a h b c h' := by
    rw [mul_comm b, mul_comm c]
    exact mul_le_mul_left a h' h

instance : PosMulStrictMono ZFInt where
  mul_lt_mul_of_pos_left _ h _ _ h' := mul_lt_mul_of_pos_left h' h
instance : MulPosStrictMono ZFInt where
  mul_lt_mul_of_pos_right _ h _ _ h' := mul_lt_mul_of_pos_right h' h

end ZFInt

noncomputable abbrev Int := Nat.prod {∅} ∪ ZFSet.prod {∅} Nat

def ZFInt.ofZFNat (n : ZFNat) : ZFInt := ZFInt.mk ⟨n, 0⟩

noncomputable def ofInt : ℤ → ZFSet
  | .ofNat n => ZFSet.pair ∅ (n : ZFNat)
  | .negSucc n => ZFSet.pair (n+1 : ZFNat) ∅

noncomputable def toZFInt : ℤ → ZFInt
  | .ofNat n => ZFInt.mk (0, ↑n)
  | .negSucc n => ZFInt.mk (↑n+1, 0)

example : ofInt 0 = {{∅}} := by
  dsimp [ofInt, pair]
  ext x
  simp only [Nat.cast_zero, mem_insert_iff, mem_singleton, or_iff_left_iff_imp]
  intro
  subst x
  ext x
  simp only [mem_insert_iff, mem_singleton, or_iff_left_iff_imp]
  exact id

section -- could be another definition
private def ofInt' : (n : ℤ) → PSet
  | .ofNat 0 => {{∅}}
  | .ofNat (n+1) => {{∅}, {∅, .ofNat n}} -- (0, n)
  | .negSucc n => {{.ofNat (n+1)}, {∅, .ofNat (n+1)}} -- (n, 0)

def PInt' : PSet := ⟨ULift ℤ, fun n => ofInt' n.down⟩
def Int' : ZFSet := ZFSet.mk PInt'
end

theorem ZFNat.mem_lift_lift_Nat (n : ℕ) : ↑(↑n : ZFNat) ∈ Nat := by
  induction n with
  | zero => simp only [Nat.cast_zero, ZFNat.nat_zero_eq, ZFNat.zero_in_Nat]
  | succ n ih =>
    simp only [Nat.cast_succ, ZFNat.add_one_eq_succ, ZFNat.succ]
    exact ZFNat.succ_mem_Nat' ih

theorem mem_ofInt_Int (n : ℤ) : ofInt n ∈ Int := by
  induction n using Int.recOn with
  | ofNat n =>
    rw [Int, mem_union, ofInt]
    right
    rw [pair_mem_prod]
    exact ⟨singleton_subset_mem_iff.mp fun _ => id, ZFNat.mem_lift_lift_Nat n⟩
  | negSucc n =>
    rw [Int, mem_union, ofInt]
    left
    rw [pair_mem_prod]
    exact ⟨ZFNat.mem_lift_lift_Nat (n+1), singleton_subset_mem_iff.mp fun _ => id⟩

theorem sub_ofInt_singleton_Int (n : ℤ) : {ofInt n} ⊆ Int := by
  intro
  rw [mem_singleton]
  rintro rfl
  exact mem_ofInt_Int n

lemma Int.nonempty : ZFSet.Int ≠ ∅ := by
  intro h
  rw [ZFSet.ext_iff] at h
  simp only [notMem_empty, iff_false] at h
  nomatch h (ZFSet.ofInt 0) (ZFSet.mem_ofInt_Int 0)

def π₁ (x : ZFSet) : ZFSet := ⋃₀ (⋂₀ x)

open Classical in -- couldn't find another way
noncomputable def π₂ (x : ZFSet) : ZFSet :=
  let δ : ZFSet := (⋃₀ x \ ⋂₀ x)
  if δ = ∅ then π₁ x else ⋃₀ δ

@[simp] theorem π₁_pair (x y : ZFSet) : π₁ (x.pair y) = x := by
  unfold π₁ pair
  ext
  rw [sInter_pair, mem_sUnion]
  constructor
  · rintro ⟨w, l, r⟩
    rw [mem_inter, mem_singleton, mem_pair] at l
    rw [l.1] at r
    assumption
  · intro h
    exists x
    rw [mem_inter, mem_singleton, mem_pair]
    exact ⟨⟨rfl, .inl rfl⟩, h⟩

@[simp] theorem pair_inter {x y : ZFSet} : {x} ∩ {x, y} = ({x} : ZFSet) := by
    ext
    rw [mem_inter, mem_singleton, mem_pair]
    constructor
    · rintro ⟨rfl, _ | rfl⟩ <;> rfl
    · rintro rfl
      exact ⟨rfl, .inl rfl⟩

@[simp] theorem pair_union {x y : ZFSet} : {x} ∪ {x, y} = ({x, y} : ZFSet) := by
    ext
    rw [mem_union, mem_singleton, mem_pair]
    exact or_self_left

@[simp] theorem pair_minus {x y : ZFSet} : x ≠ y → {x, y} \ {x} = ({y} : ZFSet) := by
  intro x_ne_y
  ext z
  rw [mem_sdiff, mem_pair, mem_singleton, mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, r⟩
    · contradiction
    · rfl
  · rintro rfl
    exact ⟨.inr rfl, x_ne_y ∘ Eq.symm⟩

@[simp] theorem π₂_pair (x y : ZFSet) : π₂ (x.pair y) = y := by
  unfold π₂
  dsimp
  split_ifs with h
  · rw [π₁_pair]
    unfold pair at h
    rw [sUnion_pair, pair_union, sInter_pair, pair_inter] at h
    rw [ZFSet.ext_iff] at h
    specialize h y
    simpa only [mem_sdiff, mem_insert_iff, mem_singleton, eq_self,
      or_true, true_and, notMem_empty, iff_false, not_not, eq_comm] using h
  · unfold pair at *
    rw [sUnion_pair, pair_union, sInter_pair, pair_inter] at h ⊢
    rw [pair_minus]
    · exact sUnion_singleton
    · intro h'
      rw [h'] at h
      simp [ZFSet.ext_iff] at h

theorem pair_eta {z A B : ZFSet} (h : z ∈ A.prod B) : z = z.π₁.pair z.π₂ := by
  rw [mem_prod] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  rw [π₁_pair, π₂_pair]

theorem mem_Int_proj {x : ZFSet} (h : x ∈ Int) :
  ∃ n ∈ Nat, (x.π₁ = ∅ ∧ x.π₂ = n) ∨ (x.π₁ = n ∧ x.π₂ = ∅) := by
  simp_rw [mem_union, mem_prod] at h
  rcases h with ⟨a, ha, b, hb, x_eq⟩ | ⟨b, hb, a, ha, x_eq⟩
    <;> (simp only [mem_singleton] at hb; subst x_eq; rw [π₁_pair, π₂_pair]; exists a)
  · exact ⟨ha, .inr ⟨rfl, hb⟩⟩
  · exact ⟨ha, .inl ⟨hb, rfl⟩⟩

theorem mem_Int_proj' {x : ZFSet} :
  x ∈ Int → (x.π₁ = ∅ ∧ x.π₂ ∈ Nat) ∨ (x.π₁ ∈ Nat ∧ x.π₂ = ∅) := by
  intro h
  rcases mem_Int_proj h with ⟨n, hn, ⟨l, r⟩ | ⟨l, r⟩⟩
  · left
    exact ⟨l, r ▸ hn⟩
  · right
    exact ⟨l ▸ hn, r⟩

open Classical in
/--
Canonical projection from a set-theoretic integer (an element of `ZFSet.Int`) to its `ZFInt`
counterpart. Given an element of `Int`, which by `mem_Int_proj'` is of the form `pair ∅ n` or
`pair n ∅` for some `n ∈ Nat`, returns `mk (0, n)` or `mk (n, 0)` respectively. The definition is
deterministic and does not depend on Schröder–Bernstein.
-/
noncomputable def ZFInt.outof : {x // x ∈ Int} → ZFInt := fun ⟨n, hn⟩ =>
  have := mem_Int_proj' hn
  if case : n.π₁ = ∅ ∧ n.π₂ ∈ Nat then
    ZFInt.mk ⟨0, n.π₂, case.right⟩
  else
    ZFInt.mk ⟨⟨n.π₁, Or.resolve_left this case |>.left⟩, 0⟩

theorem ZFInt.outof_inj (x y : {x // x ∈ Int}) : outof x = outof y → x = y := by
  let ⟨x, hx⟩ := x
  let ⟨y, hy⟩ := y
  simp only [outof, Subtype.mk.injEq]
  intro outof_eq
  split_ifs at outof_eq with h₁ h₂ h₂
    <;> (
      first
      | obtain ⟨l₁, r₁⟩ := h₁
      | obtain ⟨l₁, r₁⟩ := Or.resolve_left (mem_Int_proj' hx) h₁
      first
      | obtain ⟨l₂, r₂⟩ := h₂
      | obtain ⟨l₂, r₂⟩ := Or.resolve_left (mem_Int_proj' hy) h₂
    )
  · apply exact at outof_eq
    simp only [ZFSet.zrel, _root_.zero_add, _root_.add_zero, Subtype.mk.injEq] at outof_eq
    simp_rw [mem_union, mem_prod] at hx hy
    rcases hx, hy with ⟨⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩,⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩⟩
      <;> (simp [π₁_pair, π₂_pair] at l₁ r₁ l₂ r₂ outof_eq; subst_eqs; congr)
  · apply exact at outof_eq
    simp only [ZFSet.zrel, _root_.add_zero] at outof_eq
    obtain ⟨l₃, r₃⟩ := ZFNat.eq_zero_of_add_eq_zero outof_eq.symm
    injection l₃ with l₃
    injection r₃ with r₃
    simp_rw [mem_union, mem_prod] at hx hy
    rcases hx, hy with ⟨⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩,⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩⟩
      <;> (simp [π₁_pair, π₂_pair] at l₁ r₁ l₂ r₂ l₃ r₃ outof_eq; subst_eqs; congr)
  · apply exact at outof_eq
    simp only [ZFSet.zrel, _root_.add_zero] at outof_eq
    obtain ⟨l₃, r₃⟩ := ZFNat.eq_zero_of_add_eq_zero outof_eq
    injection l₃ with l₃
    injection r₃ with r₃
    simp_rw [mem_union, mem_prod] at hx hy
    rcases hx, hy with ⟨⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩,⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩⟩
      <;> (simp [π₁_pair, π₂_pair] at l₁ r₁ l₂ r₂ l₃ r₃ outof_eq; subst_eqs; congr)
  · apply exact at outof_eq
    simp only [ZFSet.zrel, _root_.add_zero, _root_.zero_add, Subtype.mk.injEq] at outof_eq
    simp_rw [mem_union, mem_prod] at hx hy
    rcases hx, hy with ⟨⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩,⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩⟩
      <;> (simp [π₁_pair, π₂_pair] at l₁ r₁ l₂ r₂ outof_eq; subst_eqs; congr)

theorem ZFNat.mem_Nat_sub_one {n : ZFNat} : (n - 1).1 ∈ Nat := by
  induction n with
  | zero => rw [ZFNat.zero_sub]; exact ZFNat.zero_in_Nat
  | succ n _ =>
    rw [ZFNat.sub_one_eq_pred, ZFNat.add_one_eq_succ, ZFNat.pred_succ]
    rcases n; simpa

theorem ZFNat.mem_Nat_sub {n m : ZFNat} : (n - m).1 ∈ Nat := by
  induction m with
  | zero => rcases n; simpa
  | succ m _ =>
    rw [ZFNat.sub_add_distrib]
    exact ZFNat.mem_Nat_sub_one

theorem mem_Int_empty_not_mem {x : ZFSet} {h : x ∈ Int} : ∅ ∉ x := by
  intro contr
  simp_rw [mem_union, mem_prod] at h
  rcases h with ⟨a, _, b, _, h⟩ | ⟨a, _, b, _, h⟩
  all_goals
    unfold pair at h
    subst h
    rw [mem_insert_iff, mem_singleton] at contr
    rcases contr with contr | contr
    all_goals
      simp only [ZFSet.ext_iff, notMem_empty, false_iff] at contr
      specialize contr a
      simp at contr

/-! ## Well-definedness of `ZFInt` with respect to `ZFSet.Int` -/
noncomputable section ZFIntEquivInt

open Classical in
/--
This function maps `ZFInt` to `Int` by taking the first projection of the pair.
-/
def ZFInt.into (x : ZFInt) : {x // x ∈ Int} :=
  let ⟨a,b⟩ := x.out
  if a < b then
    let n := ZFSet.pair ∅ (b-a).1
    have : n ∈ Int := by
      rw [mem_union]
      right
      rw [mem_prod]
      exact ⟨∅, mem_singleton.mpr rfl, (b-a).1, ZFNat.mem_Nat_sub, rfl⟩
    ⟨n, this⟩
  else
    let n := ZFSet.pair (a-b).1 ∅
    have : n ∈ Int := by
      rw [mem_union]
      left
      rw [mem_prod]
      exact ⟨(a-b).1, ZFNat.mem_Nat_sub, ∅, mem_singleton.mpr rfl, rfl⟩
    ⟨n, this⟩

theorem ZFInt.into_inj_aux (x y : ZFInt) : into x = into y → x.out ≈ y.out := by
  dsimp [into]
  obtain ⟨a, b⟩ := Quotient.out x
  obtain ⟨c, d⟩ := Quotient.out y
  split_ifs with h₁ h₂ h₂ <;>
    (intro eq;
     simp only [not_lt, Subtype.mk.injEq, pair_inj, SetLike.coe_eq_coe, true_and,
       and_true] at *)
  · have := ZFNat.eq_add_of_sub_eq (hle := .inl h₁) (h := eq)
    rw [ZFNat.add_comm, ← ZFNat.add_sub_assoc (.inl h₂)] at this
    apply ZFNat.eq_add_of_sub_eq (h := this.symm)
    rw [ZFNat.add_comm]
    exact ZFNat.le_trans (.inl h₂) (ZFNat.le_add_right d a)
  · obtain ⟨eq₁, eq₂⟩ := eq
    replace eq₁ : 0 = c - d := Subtype.ext eq₁
    replace eq₂ : b - a = 0 := Subtype.ext eq₂
    have := ZFNat.le_antisymm (ZFNat.sub_eq_zero_imp_le.mp (eq₁.symm)) h₂
    subst this
    rw [eq₁] at eq₂
    apply ZFNat.eq_add_of_sub_eq (.inl h₁) at eq₂
    rw [ZFNat.add_comm, ← ZFNat.add_sub_assoc h₂] at eq₂
    symm at eq₂
    apply ZFNat.eq_add_of_sub_eq (h := eq₂)
    exact ZFNat.le_add_left c a
  · obtain ⟨eq₁, eq₂⟩ := eq
    replace eq₁ : a - b = 0 := Subtype.ext eq₁
    replace eq₂ : 0 = d - c := Subtype.ext eq₂
    have := ZFNat.le_antisymm (ZFNat.sub_eq_zero_imp_le.mp eq₁) h₁
    subst this
    rw [eq₂] at eq₁
    apply ZFNat.eq_add_of_sub_eq h₁ at eq₁
    rw [ZFNat.add_comm, ← ZFNat.add_sub_assoc (.inl h₂)] at eq₁
    symm at eq₁
    apply ZFNat.eq_add_of_sub_eq (h := eq₁)
    left
    rw [← @ZFNat.zero_add c]
    apply ZFNat.add_lt_add_of_le_of_lt
    · exact ZFNat.zero_le
    · assumption
  · have := ZFNat.eq_add_of_sub_eq (hle := h₁) (h := eq)
    rw [ZFNat.add_comm, ← ZFNat.add_sub_assoc h₂] at this
    apply Eq.symm ∘ ZFNat.eq_add_of_sub_eq (h := this.symm)
    exact ZFNat.le_trans h₂ (ZFNat.le_add_left c b)

theorem ZFInt.into_inj (x y : ZFInt) : into x = into y → x = y := by
  intro h
  apply ZFInt.into_inj_aux at h
  exact Quotient.out_equiv_out.mp h

theorem ZFInt.into.injective : Function.Injective into := into_inj
theorem ZFInt.outof.injective : Function.Injective outof := outof_inj

def ZFInt.EmbeddingZFIntInt : ZFInt ↪ {x // x ∈ Int} where
  toFun := into
  inj' := into.injective
def ZFInt.EmbeddingIntZFInt : {x // x ∈ Int} ↪ ZFInt where
  toFun := outof
  inj' := outof.injective

/--
`outof` is a left inverse of `into`. This is the key fact making `outof`/`into` a canonical pair
of inverse bijections between `ZFInt` and `{x // x ∈ Int}`, removing the need for an abstract
Schröder–Bernstein bijection.
-/
theorem ZFInt.outof_into (x : ZFInt) : outof (into x) = x := by
  conv_rhs => rw [← Quotient.out_eq x]
  unfold into
  generalize x.out = p
  obtain ⟨a, b⟩ := p
  dsimp only
  by_cases hab : a < b
  · rw [if_pos hab]
    simp only [outof]
    have h_cond : (ZFSet.pair (∅ : ZFSet) (b - a).1).π₁ = ∅ ∧
                  (ZFSet.pair (∅ : ZFSet) (b - a).1).π₂ ∈ Nat :=
      ⟨π₁_pair _ _, by rw [π₂_pair]; exact ZFNat.mem_Nat_sub⟩
    rw [dif_pos h_cond]
    refine sound ?_
    change (0 : ZFNat) + b = ⟨_, h_cond.2⟩ + a
    have hπ₂ : (⟨(ZFSet.pair (∅ : ZFSet) (b - a).1).π₂, h_cond.2⟩ : ZFNat) = b - a :=
      Subtype.ext (π₂_pair _ _)
    rw [hπ₂, ZFNat.zero_add, ZFNat.sub_add_cancel (Or.inl hab)]
  · rw [if_neg hab]
    simp only [outof]
    by_cases hcond : (ZFSet.pair (a - b).1 (∅ : ZFSet)).π₁ = ∅ ∧
                     (ZFSet.pair (a - b).1 (∅ : ZFSet)).π₂ ∈ Nat
    · rw [dif_pos hcond]
      have h_sub_zero : a - b = 0 :=
        Subtype.ext ((π₁_pair (a - b).1 (∅ : ZFSet)).symm.trans hcond.1)
      have h_le_ab : a ≤ b := ZFNat.sub_eq_zero_imp_le.mp h_sub_zero
      have h_le_ba : b ≤ a := by push Not at hab; exact hab
      have ha_eq_b : a = b := ZFNat.le_antisymm h_le_ab h_le_ba
      subst ha_eq_b
      refine sound ?_
      change (0 : ZFNat) + a = _ + a
      have hπ₂ : (⟨(ZFSet.pair (a - a).1 (∅ : ZFSet)).π₂, hcond.2⟩ : ZFNat) = 0 :=
        Subtype.ext (π₂_pair _ _)
      rw [hπ₂]
    · rw [dif_neg hcond]
      push Not at hab
      -- Rewrite `π₁ (pair (a-b).1 ∅)` to `(a-b).1` via `simp` (which handles the dependent
      -- proof in the inner ZFNat subtype); then proof irrelevance makes `⟨(a-b).1, _⟩`
      -- definitionally `a - b`.
      simp only [π₁_pair]
      refine sound ?_
      change (a - b) + b = (0 : ZFNat) + a
      rw [ZFNat.zero_add]
      exact ZFNat.sub_add_cancel hab

/-- `into` is a right inverse of `outof`. -/
theorem ZFInt.into_outof (y : {x // x ∈ Int}) : into (outof y) = y :=
  outof_inj _ _ (outof_into _)

attribute [-instance] ZFSet.instPartialOrder

/--
Canonical linear order on the set-theoretic integers, defined as the pullback of the linear order
on `ZFInt` along the canonical projection `outof`. With this definition, statements like `0 < 1`
on `{x // x ∈ Int}` reduce to the corresponding statements on `ZFInt`, so they are decidable —
unlike the previous Schröder–Bernstein-based definition, which made specific instances of `<`
unprovable.
-/
noncomputable instance instLinearOrderSubtypeMemInt : LinearOrder {x // x ∈ Int} where
  le x y := ZFInt.outof x ≤ ZFInt.outof y
  lt x y := ZFInt.outof x < ZFInt.outof y
  le_refl x := le_refl (ZFInt.outof x)
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  lt_iff_le_not_ge x y :=
    lt_iff_le_not_ge (a := ZFInt.outof x) (b := ZFInt.outof y)
  le_antisymm _ _ h₁ h₂ := ZFInt.outof_inj _ _ (le_antisymm h₁ h₂)
  le_total x y := le_total (ZFInt.outof x) (ZFInt.outof y)
  toDecidableLE _ _ := Classical.propDecidable _

/--
The type `ZFInt` is in canonical bijection with the subtype `{x // x ∈ ZFSet.Int}`. The
equivalence is built directly from `ZFInt.into` and `ZFInt.outof` — no Schröder–Bernstein, no
`Classical.choice` over a non-empty set of bijections. In particular, `instEquivZFIntInt x` is
deterministic in `x`.
-/
@[reducible]
noncomputable def instEquivZFIntInt : ZFInt ≃ {x // x ∈ Int} where
  toFun := ZFInt.into
  invFun := ZFInt.outof
  left_inv := ZFInt.outof_into
  right_inv := ZFInt.into_outof

instance : Coe ZFInt {x // x ∈ Int} := ⟨instEquivZFIntInt.toFun⟩
instance : Coe {x // x ∈ Int} ZFInt := ⟨instEquivZFIntInt.invFun⟩

/--
The canonical equivalence preserves order: the strict order on `{x // x ∈ Int}` is exactly the
pullback of the strict order on `ZFInt` along `instEquivZFIntInt.invFun = ZFInt.outof`.
-/
theorem instEquivZFIntInt.mono_iff (x y : {x // x ∈ Int}) :
    instEquivZFIntInt.invFun x < instEquivZFIntInt.invFun y ↔ x < y :=
  Iff.rfl

/--
Regression check addressing the well-definedness reviewer comment: with the canonical order on
`{x // x ∈ Int}`, `0 < 1` is decidable. Specifically, the images of `(0 : ZFInt)` and
`(1 : ZFInt)` under the canonical equivalence satisfy strict inequality, and the proof reduces
to `ZFInt.zero_lt_one` after unfolding `outof ∘ into`.
-/
example :
    (instEquivZFIntInt (0 : ZFInt) : {x // x ∈ Int}) < instEquivZFIntInt (1 : ZFInt) := by
  change ZFInt.outof (ZFInt.into 0) < ZFInt.outof (ZFInt.into 1)
  rw [ZFInt.outof_into, ZFInt.outof_into]
  exact ZFInt.zero_lt_one

end ZFIntEquivInt
/-! ## Euclidean division

`ZFInt` is equipped with both common integer-division conventions, transported along the
canonical ring equivalence from `ZFInt` to `ℤ`.

The higher-priority Euclidean-domain instance makes `/` and `%` use `Int.ediv` and `Int.emod`; for
`b ≠ 0`, its remainder satisfies `0 ≤ a % b < |b|`. Floor division remains available through the
explicitly named `fdiv` and `fmod` operations and through the lower-priority
`floorEuclideanDomain` instance.
-/

namespace ZFInt

universe u

noncomputable section

instance instNontrivial : Nontrivial ZFInt :=
  ⟨⟨1, 0, one_ne_zero⟩⟩

instance instCharZero : CharZero ZFInt :=
  AddMonoidWithOne.toCharZero

private theorem intCast_surjective : Function.Surjective (Int.cast : ℤ → ZFInt) := by
  intro z
  induction z using ZFInt.induction with
  | zero =>
      exact ⟨0, rfl⟩
  | pos z ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, by rw [Int.cast_add, Int.cast_one]⟩
  | neg z ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n - 1, by rw [Int.cast_sub, Int.cast_one]⟩

/-- The canonical ring equivalence between the quotient construction `ZFInt` and Lean's `ℤ`. -/
def equivInt : ZFInt ≃+* ℤ :=
  (RingEquiv.ofBijective (Int.castRingHom ZFInt)
    ⟨Int.cast_injective, intCast_surjective⟩).symm

@[simp]
theorem equivInt_intCast (z : ℤ) : equivInt (z : ZFInt) = z := by
  change equivInt (equivInt.symm z) = z
  exact equivInt.apply_symm_apply z

@[simp]
theorem intCast_equivInt (z : ZFInt) : ((equivInt z : ℤ) : ZFInt) = z := by
  change equivInt.symm (equivInt z) = z
  exact equivInt.symm_apply_apply z

theorem equivInt_le (a b : ZFInt) : equivInt a ≤ equivInt b ↔ a ≤ b := by
  constructor <;> intro h
  · have h' : ((equivInt a : ℤ) : ZFInt) ≤ ((equivInt b : ℤ) : ZFInt) :=
      Int.cast_mono h
    rwa [intCast_equivInt, intCast_equivInt] at h'
  · rwa [← intCast_equivInt a, ← intCast_equivInt b, Int.cast_le] at h

theorem equivInt_lt (a b : ZFInt) : equivInt a < equivInt b ↔ a < b := by
  rw [lt_iff_not_ge, lt_iff_not_ge, equivInt_le]

@[simp]
theorem equivInt_abs (z : ZFInt) : equivInt |z| = |equivInt z| := by
  rcases _root_.le_total 0 z with hz | hz
  · have hz' : (0 : ℤ) ≤ equivInt z := by
      rwa [←equivInt_le 0 z, map_zero] at hz
    rw [abs_of_nonneg hz, abs_of_nonneg hz']
  · have hz' : equivInt z ≤ (0 : ℤ) := by
      rwa [←equivInt_le z 0, map_zero] at hz
    rw [abs_of_nonpos hz, abs_of_nonpos hz', map_neg]

@[reducible] private def intFloorEuclideanDomain : EuclideanDomain ℤ :=
  { (inferInstance : CommRing ℤ), (inferInstance : Nontrivial ℤ) with
    quotient := Int.fdiv
    quotient_zero := Int.fdiv_zero
    remainder := Int.fmod
    quotient_mul_add_remainder_eq := Int.mul_fdiv_add_fmod
    r := fun a b ↦ a.natAbs < b.natAbs
    r_wellFounded := (measure Int.natAbs).wf
    remainder_lt := by
      intro a b hb
      rcases lt_or_gt_of_ne hb with hb | hb
      · have hbounds :=
          (Int.fdiv_fmod_unique' (a := a) (b := b) (r := a.fmod b) (q := a.fdiv b) hb).mp
            ⟨rfl, rfl⟩
        simpa only [Int.natAbs_neg] using
          Int.natAbs_lt_natAbs_of_nonneg_of_lt
            (Int.neg_nonneg_of_nonpos hbounds.2.2) (Int.neg_lt_neg hbounds.2.1)
      · exact Int.natAbs_lt_natAbs_of_nonneg_of_lt
          (Int.fmod_nonneg_of_pos a hb) (Int.fmod_lt_of_pos a hb)
    mul_left_not_lt := fun a b hb ↦
      not_lt_of_ge <| by
        rw [← Int.natAbs_pos] at hb
        grw [← Nat.mul_one a.natAbs, Int.natAbs_mul, Nat.mul_le_mul_left _ hb]
  }

/-- The floor-division Euclidean-domain structure on `ZFInt`. -/
@[reducible] def floorEuclideanDomain : EuclideanDomain ZFInt := by
  letI : EuclideanDomain ℤ := intFloorEuclideanDomain
  exact equivInt.euclideanDomain

/-- The nonnegative-remainder Euclidean-domain structure on `ZFInt`. -/
@[reducible] def edivEuclideanDomain : EuclideanDomain ZFInt :=
  equivInt.euclideanDomain

/-- The floor convention remains available as a lower-priority instance. -/
instance (priority := low) instFloorEuclideanDomain : EuclideanDomain ZFInt :=
  floorEuclideanDomain

/-- The `ediv` convention is the default convention used by `/` and `%`. -/
instance (priority := high) instEuclideanDomain : EuclideanDomain ZFInt :=
  edivEuclideanDomain

@[simp]
theorem equivInt_div (a b : ZFInt) : equivInt (a / b) = equivInt a / equivInt b :=
  equivInt.apply_symm_apply _

@[simp]
theorem equivInt_mod (a b : ZFInt) : equivInt (a % b) = equivInt a % equivInt b :=
  equivInt.apply_symm_apply _

theorem div_add_mod (a b : ZFInt) : b * (a / b) + a % b = a :=
  EuclideanDomain.div_add_mod a b

theorem mod_nonneg (a : ZFInt) {b : ZFInt} (hb : b ≠ 0) : 0 ≤ a % b := by
  apply (equivInt_le 0 (a % b)).mp
  rw [equivInt_mod, map_zero]
  apply Int.emod_nonneg
  intro hb'
  apply hb
  apply equivInt.injective
  rw [hb', map_zero]

theorem mod_lt_abs (a : ZFInt) {b : ZFInt} (hb : b ≠ 0) : a % b < |b| := by
  apply (equivInt_lt (a % b) |b|).mp
  rw [equivInt_mod, equivInt_abs]
  apply Int.emod_lt_abs
  intro hb'
  apply hb
  apply equivInt.injective
  rw [hb', map_zero]

@[simp]
theorem mod_eq_zero {a b : ZFInt} : a % b = 0 ↔ b ∣ a :=
  EuclideanDomain.mod_eq_zero

/-! ## Explicit Euclidean division -/

/-- Euclidean quotient with a nonnegative remainder. This is also the operation used by `/`. -/
def ediv (a b : ZFInt.{u}) : ZFInt.{u} :=
  equivInt.symm (equivInt a / equivInt b)

/-- Euclidean remainder in the interval `[0, |b|)` when `b ≠ 0`.
This is also the operation used by `%`. -/
def emod (a b : ZFInt.{u}) : ZFInt.{u} :=
  equivInt.symm (equivInt a % equivInt b)

@[simp]
theorem equivInt_ediv (a b : ZFInt) :
    equivInt (ediv a b) = equivInt a / equivInt b :=
  equivInt.apply_symm_apply _

@[simp]
theorem equivInt_emod (a b : ZFInt) :
    equivInt (emod a b) = equivInt a % equivInt b :=
  equivInt.apply_symm_apply _

@[simp]
theorem ediv_eq_div (a b : ZFInt) : ediv a b = a / b := by
  apply equivInt.injective
  rw [equivInt_ediv, equivInt_div]

@[simp]
theorem emod_eq_mod (a b : ZFInt) : emod a b = a % b := by
  apply equivInt.injective
  rw [equivInt_emod, equivInt_mod]

theorem ediv_add_emod (a b : ZFInt) : b * ediv a b + emod a b = a := by
  erw [div_add_mod a b]

theorem emod_nonneg (a : ZFInt) {b : ZFInt} (hb : b ≠ 0) : 0 ≤ emod a b := by
  apply (equivInt_le 0 (emod a b)).mp
  rw [equivInt_emod, map_zero]
  apply Int.emod_nonneg
  intro hb'
  apply hb
  apply equivInt.injective
  rw [hb', map_zero]

theorem emod_lt_abs (a : ZFInt) {b : ZFInt} (hb : b ≠ 0) : emod a b < |b| := by
  apply (equivInt_lt (emod a b) |b|).mp
  rw [equivInt_emod, equivInt_abs]
  apply Int.emod_lt_abs
  intro hb'
  apply hb
  apply equivInt.injective
  rw [hb', map_zero]

@[simp]
theorem emod_eq_zero {a b : ZFInt} : emod a b = 0 ↔ b ∣ a := by
  constructor <;> intro h
  · apply (map_dvd_iff equivInt).mp
    rw [Int.dvd_iff_emod_eq_zero, ←equivInt_emod, h, map_zero]
  · apply equivInt.injective
    rwa [equivInt_emod, map_zero, ← Int.dvd_iff_emod_eq_zero, map_dvd_iff equivInt]

/-! ## Explicit floor division -/

/-- Floor quotient: the quotient of `a` by `b`, rounded toward negative infinity. -/
def fdiv (a b : ZFInt.{u}) : ZFInt.{u} :=
  equivInt.symm ((equivInt a).fdiv (equivInt b))

/-- Floor remainder. For a nonzero divisor, it has the sign of the divisor. -/
def fmod (a b : ZFInt.{u}) : ZFInt.{u} :=
  equivInt.symm ((equivInt a).fmod (equivInt b))

@[simp]
theorem equivInt_fdiv (a b : ZFInt) :
    equivInt (fdiv a b) = (equivInt a).fdiv (equivInt b) :=
  equivInt.apply_symm_apply _

@[simp]
theorem equivInt_fmod (a b : ZFInt) :
    equivInt (fmod a b) = (equivInt a).fmod (equivInt b) :=
  equivInt.apply_symm_apply _

theorem fdiv_add_fmod (a b : ZFInt) : b * fdiv a b + fmod a b = a := by
  apply equivInt.injective
  simp only [map_add, map_mul, equivInt_fdiv, equivInt_fmod]
  apply Int.mul_fdiv_add_fmod

theorem fmod_nonneg_of_pos (a : ZFInt) {b : ZFInt} (hb : 0 < b) : 0 ≤ fmod a b := by
  apply (equivInt_le 0 (fmod a b)).mp
  rw [equivInt_fmod, map_zero]
  apply Int.fmod_nonneg_of_pos
  rwa [←equivInt_lt 0 b, map_zero] at hb

theorem fmod_lt_of_pos (a : ZFInt) {b : ZFInt} (hb : 0 < b) : fmod a b < b := by
  apply (equivInt_lt (fmod a b) b).mp
  rw [equivInt_fmod]
  apply Int.fmod_lt_of_pos
  rwa [←equivInt_lt 0 b, map_zero] at hb

theorem fmod_nonpos_of_neg (a : ZFInt) {b : ZFInt} (hb : b < 0) : fmod a b ≤ 0 := by
  apply (equivInt_le (fmod a b) 0).mp
  rw [equivInt_fmod, map_zero]
  have hb' : equivInt b < (0 : ℤ) := by
    rwa [← equivInt_lt b 0, map_zero] at hb
  exact ((Int.fdiv_fmod_unique' hb').mp ⟨rfl, rfl⟩).2.2

theorem lt_fmod_of_neg (a : ZFInt) {b : ZFInt} (hb : b < 0) : b < fmod a b := by
  apply (equivInt_lt b (fmod a b)).mp
  rw [equivInt_fmod]
  have hb' : equivInt b < (0 : ℤ) := by
    rwa [← equivInt_lt b 0, map_zero] at hb
  exact ((Int.fdiv_fmod_unique' hb').mp ⟨rfl, rfl⟩).2.1

@[simp]
theorem fmod_eq_zero {a b : ZFInt} : fmod a b = 0 ↔ b ∣ a := by
  calc
    fmod a b = 0 ↔ equivInt (fmod a b) = equivInt 0 := equivInt.injective.eq_iff.symm
    _ ↔ (equivInt a).fmod (equivInt b) = 0 := by rw [equivInt_fmod, map_zero]
    _ ↔ equivInt b ∣ equivInt a := Int.dvd_iff_fmod_eq_zero.symm
    _ ↔ b ∣ a := map_dvd_iff equivInt

end

end ZFInt

/-! ## Transfer to `ℤ`

`equivInt` is registered as a `TransferEquiv`, so that the `transfer` tactic reads a goal about
`ZFInt` in `ℤ`:

```
example (a b : ZFInt) : a + b = b + a := by
  transfer ZFInt → ℤ =>
    rw [Int.add_comm]
```

The ring operations, the numerals and the casts travel through the generic `map_…` lemmas of the
`transfer_simps` simp set; the order relations and the two division conventions are the lemmas
proved above, tagged here.
-/

section Transfer

namespace ZFInt

/-- Equivalence used by the `transfer` tactic to move goals between `ZFInt` and `ℤ`. -/
noncomputable instance : TransferEquiv ZFInt ℤ := ⟨equivInt.toEquiv⟩

/-- Divisibility is read in `ℤ`; `map_dvd_iff` reads the wrong way round for `transfer`. -/
@[transfer_simps] theorem equivInt_dvd (a b : ZFInt) :
    a ∣ b ↔ equivInt a ∣ equivInt b := (map_dvd_iff equivInt).symm

attribute [transfer_simps ←] equivInt_le equivInt_lt

attribute [transfer_simps] equivInt_abs equivInt_div equivInt_mod equivInt_ediv equivInt_emod
  equivInt_fdiv equivInt_fmod

end ZFInt

end Transfer

end Integers
end ZFSet

end
