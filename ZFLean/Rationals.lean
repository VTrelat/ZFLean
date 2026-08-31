/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import ZFLean.Integers
import ZFLean.TransferAlgebra
public import ZFLean.Quotient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring

/-! # ZFC Rational Numbers

This file defines the rational numbers in ZFC, based on the integers and using the `ZFInt` type.

-/

public section

namespace ZFSet

section Rationals

abbrev ZFInt' := {x : ZFInt // x ≠ 0}

/-- The equivalence relation on `ℤ × ℤ⋆` that defines the rational numbers. -/
protected abbrev qrel (p q : ZFInt × ZFInt') : Prop := p.1 * q.2 = p.2 * q.1

protected def qrel_eq : Equivalence ZFSet.qrel where
  refl x := ZFInt.mul_comm x.1 x.2
  symm h := by
    unfold ZFSet.qrel at h ⊢
    rw [ZFInt.mul_comm, ←h, ZFInt.mul_comm]
  trans := by
    rintro ⟨p, q, hq⟩ ⟨u, v, hv⟩ ⟨s, t, ht⟩ hpq huv
    dsimp [ZFSet.qrel] at hpq huv ⊢
    -- have : p * v * u * t = q * u * s * v := by
    have : p * t * u * v = q * s * u * v := by
      suffices p * v * u * t = q * u * s * v by
        rw [
          mul_assoc, mul_assoc,
          mul_comm t, mul_comm u,
          ←mul_assoc, ←mul_assoc,
          this,
          mul_assoc, mul_assoc,
          mul_comm u, mul_assoc, mul_comm v,
          ←mul_assoc, ←mul_assoc]
      rw [hpq, mul_assoc, huv, mul_comm v s, ← mul_assoc]
    conv at this =>
      conv => lhs; rw [mul_assoc]
      conv => rhs; rw [mul_assoc]
    by_cases u_mul_v : u * v = 0
    · rw [ZFInt.mul_comm] at u_mul_v
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero u_mul_v hv
      rw [ZFInt.mul_zero, ZFInt.mul_comm] at hpq
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero hpq hv
      rw [ZFInt.zero_mul] at huv
      symm at huv
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero huv hv
      rw [ZFInt.mul_zero, ZFInt.zero_mul]
    · rwa [ZFInt.mul_right_cancel_iff u_mul_v] at this

/-- `ℤ × ℤ⋆` equipped with `qrel` is a setoid. -/
protected instance instSetoidZFIntZFInt' : Setoid (ZFInt × ZFInt') where
  r := ZFSet.qrel
  iseqv := ZFSet.qrel_eq

/-- `ℚ` is defined as `ℤ × ℤ⋆` quotiented by `qrel` -/
abbrev ZFRat := Quotient ZFSet.instSetoidZFIntZFInt'

namespace ZFRat

section Quotient

@[expose] def mk : ZFInt × ZFInt' → ZFRat := Quotient.mk''

@[simp]
theorem mk_eq (x : ZFInt × ZFInt') : @Eq ZFRat ⟦x⟧ (mk x) := rfl

@[simp]
theorem mk_out : ∀ x : ZFRat, mk x.out = x := Quotient.out_eq

theorem eq {x y : ZFInt × ZFInt'} : mk x = mk y ↔ ZFSet.qrel x y := Quotient.eq

theorem sound {x y : ZFInt × ZFInt'} (h : ZFSet.qrel x y) : mk x = mk y := Quotient.sound h
theorem exact {x y : ZFInt × ZFInt'} : mk x = mk y → ZFSet.qrel x y := Quotient.exact

abbrev zero : ZFRat := mk (0, ⟨1, ZFInt.one_ne_zero⟩)
abbrev one : ZFRat := mk (1, ⟨1, ZFInt.one_ne_zero⟩)

protected instance : Zero ZFRat := ⟨zero⟩
protected instance : One ZFRat := ⟨one⟩

instance : Inhabited ZFRat := ⟨0⟩

theorem zero_eq : (0 : ZFRat) = mk (0, ⟨1, ZFInt.one_ne_zero⟩) := rfl
theorem one_eq : (1 : ZFRat) = mk (1, ⟨1, ZFInt.one_ne_zero⟩) := rfl

theorem mk_eq_zero_iff {n m} : ZFRat.mk (n,m) = 0 ↔ n = 0 where
  mp := by
    intro h
    rw [zero_eq, eq, ZFSet.qrel] at h
    simpa only [mul_one, ne_eq, mul_zero] using h
  mpr := by
    rintro rfl
    apply ZFRat.sound
    rw [ZFSet.qrel, mul_one, mul_zero]

theorem mk_ne_zero {a : ZFInt} {b : ZFInt'} (ha : a ≠ 0) : mk (a, b) ≠ 0 := by
  rw [ne_eq, mk_eq_zero_iff]
  exact ha

theorem mk_eq_one_iff {n m} : ZFRat.mk (n,m) = 1 ↔ n = m where
  mp := by
    intro h
    rw [one_eq, eq, ZFSet.qrel] at h
    simpa only [ne_eq, mul_one] using h
  mpr := by
    rintro rfl
    apply ZFRat.sound
    rw [ZFSet.qrel, mul_one]

theorem one_ne_zero : (1 : ZFRat) ≠ 0 := by
  intro h
  rw [one_eq, zero_eq, eq, ZFSet.qrel, mul_one, mul_zero] at h
  nomatch ZFInt.one_ne_zero h

end Quotient
section Arithmetic
section Add

noncomputable abbrev add (n m : ZFRat) : ZFRat :=
  Quotient.liftOn₂ n m (fun ⟨a, b⟩ ⟨c, d⟩ ↦
    mk (a * d + b * c, ⟨b.1 * d.1, fun c ↦ nomatch d.2 (ZFInt.mul_eq_zero_of_ne_zero c b.2)⟩))
    fun ⟨x₁, x₂, hx₂⟩ ⟨y₁, y₂, hy₂⟩ ⟨u₁, u₂, hu₂⟩ ⟨v₁, v₂, hv₂⟩ hxu hyv ↦ sound (by
      have h1 : x₁ * u₂ = x₂ * u₁ := hxu
      have h2 : y₁ * v₂ = y₂ * v₁ := hyv
      simp only [ZFSet.qrel]
      conv_lhs =>
        rw [right_distrib]
        conv =>
          lhs
          rw [
            ←mul_assoc, mul_assoc x₁, mul_comm y₂, ←mul_assoc,
            h1, mul_assoc x₂, mul_comm u₁, ←mul_assoc, mul_assoc (x₂ * y₂)]
        conv =>
          rhs
          rw [
            mul_comm u₂, ←mul_assoc, mul_assoc x₂, h2,
            ←mul_assoc, mul_assoc, mul_comm v₁, ←mul_assoc, mul_assoc (x₂ * y₂)]
      rw [←left_distrib])

protected noncomputable instance : Add ZFRat := ⟨ZFRat.add⟩
theorem add_eq (n m : ZFInt × ZFInt') :
  mk n + mk m = mk (n.1 * m.2 + n.2 * m.1,
    ⟨n.2.1 * m.2.1, fun c ↦ nomatch m.2.2 (ZFInt.mul_eq_zero_of_ne_zero c n.2.2)⟩) := rfl

theorem add_assoc (n m k : ZFRat) : n + (m + k) = n + m + k := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  induction k using Quotient.ind
  rename_i n m k
  obtain ⟨n₁, n₂, hn₂⟩ := n
  obtain ⟨m₁, m₂, hm₂⟩ := m
  obtain ⟨k₁, k₂, hk₂⟩ := k
  apply ZFRat.sound
  ring

theorem add_comm (n m : ZFRat) : n + m = m + n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  rename_i n m
  obtain ⟨n₁, n₂, hn₂⟩ := n
  obtain ⟨m₁, m₂, hm₂⟩ := m
  apply ZFRat.sound
  ring

lemma add_left_comm (n m k : ZFRat) : n + (m + k) = m + (n + k) := by
  rw [add_assoc, add_assoc, add_comm n]

lemma add_right_comm (n m k : ZFRat) : (n + m) + k = (n + k) + m := by
  rw [← add_assoc, add_comm m, add_assoc]

@[simp]
theorem add_zero {x : ZFRat} : x + 0 = x := by
  induction x using Quotient.ind
  simp_rw [mk_eq, zero_eq, ZFRat.add_eq, mul_one, ne_eq, mul_zero, ZFInt.add_zero]

@[simp]
theorem zero_add {x : ZFRat} : 0 + x = x := by
  rw [add_comm, add_zero]
end Add
section Neg

protected abbrev neg (n : ZFRat) : ZFRat := Quotient.liftOn n (fun ⟨x, y⟩ => mk (-x, y))
  fun ⟨x, y, hy⟩ ⟨u, v, hv⟩ h ↦ sound (ZFSet.qrel_eq.symm (by
    dsimp [HasEquiv.Equiv, instHasEquivOfSetoid, ZFSet.instSetoidZFIntZFInt'] at h
    simp only [ZFSet.qrel] at h ⊢
    rw [←ZFInt.neg_mul_distrib, mul_comm, ←h, ZFInt.neg_mul_distrib, mul_comm]))

protected instance : Neg ZFRat := ⟨ZFRat.neg⟩
theorem neg_eq (n : ZFInt × ZFInt') : -mk n = mk (-n.1, n.2) := rfl

@[simp]
theorem neg_neg (n : ZFRat) : -(-n) = n := by
  induction n using Quotient.ind
  apply sound
  rw [_root_.neg_neg]
  exact eq.mp rfl

@[simp]
theorem neg_zero : -(0 : ZFRat) = 0 := rfl

theorem neg_inj {a b : ZFRat} : -a = -b ↔ a = b :=
  ⟨fun h => by rw [← neg_neg a, ← neg_neg b, h], congrArg _⟩

@[simp]
theorem neg_eq_zero {a : ZFRat} : -a = 0 ↔ a = 0 := ZFRat.neg_inj (b := 0)
theorem neg_ne_zero {a : ZFRat} : -a ≠ 0 ↔ a ≠ 0 := not_congr neg_eq_zero

theorem add_left_neg {a : ZFRat} : -a + a = 0 := by
  induction a using Quotient.ind
  apply sound
  ring

theorem add_right_neg (a : ZFRat) : a + -a = 0 := by
  rw [add_comm]
  exact add_left_neg

theorem neg_eq_of_add_eq_zero {a b : ZFRat} (h : a + b = 0) : -a = b := by
  rw [← @add_zero (-a), ← h, add_assoc, add_left_neg, zero_add]

theorem eq_neg_of_eq_neg {a b : ZFRat} (h : a = -b) : b = -a := by
  rw [h, neg_neg]

theorem eq_neg_comm {a b : ZFRat} : a = -b ↔ b = -a := ⟨eq_neg_of_eq_neg, eq_neg_of_eq_neg⟩

theorem neg_eq_comm {a b : ZFRat} : -a = b ↔ -b = a := by
  rw [eq_comm, eq_neg_comm, eq_comm]

theorem neg_add_cancel_left (a b : ZFRat) : -a + (a + b) = b := by
  rw [add_assoc, add_left_neg, zero_add]

theorem add_neg_cancel_left (a b : ZFRat) : a + (-a + b) = b := by
  rw [add_assoc, add_right_neg, zero_add]

theorem add_neg_cancel_right (a b : ZFRat) : a + b + -b = a := by
  rw [← add_assoc, add_right_neg, add_zero]

theorem neg_add_cancel_right (a b : ZFRat) : a + -b + b = a := by
  rw [← add_assoc, add_left_neg, add_zero]

theorem add_left_cancel {a b c : ZFRat} (h : a + b = a + c) : b = c := by
  have h₁ : -a + (a + b) = -a + (a + c) := by rw [h]
  simp only [add_assoc, add_left_neg, zero_add] at h₁
  exact h₁

@[simp]
theorem neg_add {a b : ZFRat} : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_right_neg, add_comm a, add_assoc, ← add_assoc b, add_right_neg, add_zero, add_right_neg]

end Neg
section Sub

noncomputable abbrev sub (n m : ZFRat) : ZFRat := n + -m
protected noncomputable instance : Sub ZFRat := ⟨ZFRat.sub⟩
theorem sub_eq (n m : ZFInt × ZFInt') :
  mk n - mk m = mk (n.1 * m.2 - m.1 * n.2, ⟨n.2 * m.2,
    fun c ↦ nomatch m.2.2 (ZFInt.mul_eq_zero_of_ne_zero c n.2.2)⟩) := by
  apply sound
  ring

theorem sub_eq_add_neg {a b : ZFRat} : a - b = a + -b := rfl

theorem add_neg_one (i : ZFRat) : i + -1 = i - 1 := rfl

@[simp]
theorem sub_self (a : ZFRat) : a - a = 0 := by rw [sub_eq_add_neg, add_right_neg]

@[simp]
theorem sub_zero (a : ZFRat) : a - 0 = a := by simp [sub_eq_add_neg]

@[simp]
theorem zero_sub (a : ZFRat) : 0 - a = -a := by simp [sub_eq_add_neg]

theorem sub_eq_zero_of_eq {a b : ZFRat} (h : a = b) : a - b = 0 := by rw [h, sub_self]

theorem eq_of_sub_eq_zero {a b : ZFRat} (h : a - b = 0) : a = b := by
  have : 0 + b = b := by rw [zero_add]
  have : a - b + b = b := by rwa [h]
  rwa [sub_eq_add_neg, neg_add_cancel_right] at this

theorem sub_eq_zero {a b : ZFRat} : a - b = 0 ↔ a = b := ⟨eq_of_sub_eq_zero, sub_eq_zero_of_eq⟩

theorem sub_sub (a b c : ZFRat) : a - b - c = a - (b + c) := by
  simp [sub_eq_add_neg, add_assoc]

theorem neg_sub (a b : ZFRat) : -(a - b) = b - a := by
  simp [sub_eq_add_neg, add_comm]

theorem sub_sub_self (a b : ZFRat) : a - (a - b) = b := by
  simp [sub_eq_add_neg, add_assoc, add_right_neg]

@[simp]
theorem sub_neg (a b : ZFRat) : a - -b = a + b := by simp [sub_eq_add_neg]
@[simp]
theorem sub_add_cancel (a b : ZFRat) : a - b + b = a := neg_add_cancel_right a b

@[simp]
theorem add_sub_cancel (a b : ZFRat) : a + b - b = a := add_neg_cancel_right a b

theorem add_sub_assoc (a b c : ZFRat) : a + b - c = a + (b - c) := by
  rw [sub_eq_add_neg, ← add_assoc, ← sub_eq_add_neg]

theorem sub_left_cancel (a b c : ZFRat) : a - c = b - c → a = b := by
  intro h
  rwa [← sub_eq_zero, sub_sub, sub_eq_zero, ← add_sub_assoc, add_comm, add_sub_cancel] at h

theorem sub_right_cancel (a b c : ZFRat) : c - a = c - b → a = b := by
  rw [← neg_sub a, ← neg_sub b, neg_inj]
  apply sub_left_cancel

theorem add_eq_sub_iff {a b c : ZFRat} : a + b = c ↔ a = c - b where
  mp := fun h => by rw [← h, add_sub_cancel]
  mpr := fun h => by rw [h, sub_add_cancel]

end Sub
section Mul

noncomputable abbrev nsmul : ℕ → ZFRat → ZFRat
  | 0, _ => 0
  | n+1, m => m + nsmul n m

noncomputable abbrev zsmul (n : ℤ) (x : ZFRat) : ZFRat :=
  match n with
  | .ofNat n => nsmul n x
  | .negSucc n => -nsmul (n+1) x

noncomputable abbrev mul (n m : ZFRat) : ZFRat :=
  Quotient.liftOn₂ n m
    (fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ ↦ mk (a * c,
      ⟨b * d, fun c ↦ nomatch hd (ZFInt.mul_eq_zero_of_ne_zero c hb)⟩))
    fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩ ⟨i, j, hi⟩ h h' ↦ by
      apply sound
      unfold_projs at h h'
      simp only [ZFSet.qrel] at h h' ⊢
      ac_change (a * f) * (c * j) = (b * e) * (d * i)
      rw [h, h']

noncomputable instance : Mul ZFRat := ⟨ZFRat.mul⟩
theorem mul_eq (n m : ZFInt × ZFInt') :
  mk n * mk m = mk (n.1 * m.1, ⟨n.2 * m.2,
    fun c ↦ nomatch m.2.2 (ZFInt.mul_eq_zero_of_ne_zero c n.2.2)⟩) := rfl

theorem mul_comm (n m : ZFRat) : n * m = m * n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  apply sound
  ring

theorem left_distrib (a b c : ZFRat) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply sound
  ring

theorem right_distrib (a b c : ZFRat) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm, mul_comm b c]

@[simp]
theorem zero_mul (a : ZFRat) : 0 * a = 0 := by
  induction a using Quotient.ind
  apply sound
  ring

@[simp]
theorem mul_zero (a : ZFRat) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem mul_assoc (a b c : ZFRat) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply sound
  ring

@[simp]
theorem one_mul (a : ZFRat) : 1 * a = a := by
  induction a using Quotient.ind
  apply sound
  ring

@[simp]
theorem mul_one (a : ZFRat) : a * 1 = a := by
  rw [mul_comm, one_mul]

theorem mul_eq_zero_iff {a b : ZFRat} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    induction a using Quotient.ind
    induction b using Quotient.ind
    simp_rw [mk_eq, mul_eq, zero_eq, eq, ZFSet.qrel, ZFInt.mul_zero, ZFInt.mul_one] at h ⊢
    rwa [←ZFInt.mul_eq_zero_iff]
  · rintro (h | h)
    · rw [h, zero_mul]
    · rw [h, mul_zero]

end Mul

noncomputable instance : CommRing ZFRat where
  zero := 0
  one := 1
  add := add
  add_assoc _ _ _ := by rw [add_assoc]
  zero_add _ := zero_add
  add_zero _ := add_zero
  nsmul := ZFSet.ZFRat.nsmul
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
  zsmul := ZFSet.ZFRat.zsmul
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := add_comm _ _
  zsmul_neg' _ _ := rfl
  neg_add_cancel _ := add_left_neg

theorem intCast_eq_mk (n : ℤ) :
    ((n : ℤ) : ZFRat) = mk ((n : ZFInt), ⟨1, ZFInt.one_ne_zero⟩) := by
  induction n using Int.induction_on with
  | zero => rw [Int.cast_zero, Int.cast_zero, ← zero_eq]
  | succ k ih =>
    simp only [Int.cast_add, Int.cast_one]
    rw [ih, one_eq, add_eq]
    apply sound
    rw [ZFSet.qrel]
    ring
  | pred k ih =>
    simp only [Int.cast_sub, Int.cast_one]
    rw [ih, one_eq, sub_eq]
    apply sound
    rw [ZFSet.qrel]
    ring

section Div

abbrev ZFRat' := {x : ZFRat // x ≠ 0}

protected noncomputable abbrev inv : ZFRat' → ZFRat' := fun ⟨x, hx⟩ ↦ by
  let a := x.out.1
  let hb := x.out.2.2
  set b := x.out.2.1
  have : a ≠ 0 := by
    intro contr
    have : mk (0, ⟨b, hb⟩) = x := by
      have : x.out = (0, ⟨b, hb⟩) := Prod.ext contr rfl
      rw [←this]
      exact mk_out x
    obtain rfl : x = 0 := by
      rw [←this, zero_eq, eq, ZFSet.qrel, ZFInt.mul_one, ZFInt.mul_zero]
    contradiction
  exact ⟨mk (b, ⟨a, this⟩), by
    intro h
    rw [mk_eq_zero_iff] at h
    contradiction⟩

noncomputable instance : Inv ZFRat' := ⟨ZFRat.inv⟩
open Classical in
noncomputable instance : Inv ZFRat where
  inv x := if hx : x ≠ 0 then ZFRat.inv ⟨x, hx⟩ else 0

theorem inv_eq {a : ZFRat} (ha : a ≠ 0) : a⁻¹ = (⟨a, ha⟩ : ZFRat')⁻¹ := by
  dsimp [Inv.inv]
  rw [dif_pos ha]

noncomputable abbrev hdiv (n : ZFRat) (m : ZFRat') : ZFRat := n * m⁻¹
open Classical in
noncomputable abbrev div (n m : ZFRat) : ZFRat :=
  if hm : m ≠ 0 then hdiv n ⟨m, hm⟩ else 0
noncomputable instance : HDiv ZFRat ZFRat' ZFRat := ⟨hdiv⟩
noncomputable instance : Div ZFRat := ⟨div⟩


theorem div_eq {n m : ZFRat} (hm : m ≠ 0) : n / m = n / (⟨m, hm⟩:ZFRat') := rfl
theorem div_eq_mul_inv {n m : ZFRat} (hm : m ≠ 0) : n / m = n * (⟨m, hm⟩:ZFRat')⁻¹ := by
  dsimp [HDiv.hDiv, Div.div]
  rw [div, dif_pos hm]

@[simp]
theorem mul_inv' {a : ZFRat'} : a.1 * a⁻¹ = 1 := by
  obtain ⟨a, ha⟩ := a
  induction a using Quotient.ind
  rename_i a
  apply sound
  rw [ZFSet.qrel]
  simp only [mk_eq, ZFInt.mul_one, ne_eq]
  change ZFSet.qrel ⟨a.1, ⟨a.2.1, a.2.2⟩⟩ (mk a).out
  rw [←eq]
  symm
  apply mk_out
@[simp]
theorem mul_inv {a : ZFRat} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_eq ha, @mul_inv' (⟨a, ha⟩ : ZFRat')]

@[simp]
theorem inv_mul' {a : ZFRat'} : a⁻¹ * a.1 = 1 := by
  rw [mul_comm]
  exact mul_inv'
@[simp]
theorem inv_mul {a : ZFRat} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv ha

theorem mk_eq_div (a : ZFInt) (b : ZFInt') :
    mk (a, b) = mk (a, ⟨1, ZFInt.one_ne_zero⟩) / mk (b.val, ⟨1, ZFInt.one_ne_zero⟩) := by
  have hb : mk (b.val, ⟨1, ZFInt.one_ne_zero⟩) ≠ 0 := mk_ne_zero b.2
  have key : mk (a, b) * mk (b.val, ⟨1, ZFInt.one_ne_zero⟩)
      = mk (a, ⟨1, ZFInt.one_ne_zero⟩) := by
    rw [mul_eq]
    apply sound
    rw [ZFSet.qrel]
    ring
  rw [div_eq_mul_inv hb, ← inv_eq hb, ← key, mul_assoc, mul_inv hb, mul_one]

end Div

noncomputable instance : RatCast ZFRat where
  ratCast q := ((q.num : ZFRat) / (q.den : ZFRat))

noncomputable def qsmul (k : ℚ) (m : ZFRat) : ZFRat := (k : ZFRat) * m

noncomputable def nnqsmul : ℚ≥0 → ZFRat → ZFRat :=
  fun ⟨k, _⟩ m ↦ qsmul k m

open Classical in
noncomputable instance : DivisionRing ZFRat where
  exists_pair_ne := ⟨1, 0, one_ne_zero⟩
  mul_inv_cancel _ := mul_inv
  inv_zero := by
    simp only [Inv.inv, ne_eq, not_true_eq_false, dite_false]
  div_eq_mul_inv := by
    intro a b
    by_cases hb : b = 0
    · subst b
      dsimp [HDiv.hDiv, Div.div, div, Inv.inv]
      iterate 2 rw [dite_cond_eq_false (eq_false (fun a ↦ a rfl))]
      rw [mul_zero]
    · rw [div_eq_mul_inv hb, ←inv_eq]
  qsmul := qsmul
  nnqsmul := nnqsmul
  ratCast_def _ := rfl
  qsmul_def _ _ := by rfl
  nnqsmul_def := by
    rintro ⟨k, hk⟩ m
    unfold nnqsmul qsmul
    dsimp
    unfold_projs
    have : (↑k.num.natAbs : ZFRat) = ↑k.num := by
      unfold Int.natAbs
      cases k using Rat.casesOn with
      | mk' n d hd _ =>
        simp only [Rat.le_iff, Rat.num_ofNat, MulZeroClass.zero_mul, Rat.den_ofNat, Nat.cast_one,
          _root_.mul_one] at hk
        dsimp
        have : n = Int.ofNat n.natAbs := by
          rw [Int.ofNat_eq_natCast, ←Int.eq_natAbs_of_nonneg hk]
        rw [this]
        rfl
    dsimp [NNRat.cast, NNRatCast.nnratCast, NNRat.castRec]
    rw [this]
    rfl

noncomputable instance : Field ZFRat := {}

section Order

/-- A rational is positive iff numerator and denominator carry the same sign.
Well-defined because for equivalent reps `(a,b) ≈ (c,d)` (i.e. `a*d = b*c`),
multiplying both sides by `b*d` gives `(a*b)*(d*d) = (b*b)*(c*d)`, and `b*b`,
`d*d` are both positive, so `a*b` and `c*d` share a sign. -/
def isPos (x : ZFRat) : Prop :=
  Quotient.liftOn x (fun ⟨a, b, _⟩ ↦ 0 < a * b)
    fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ h ↦ by
      unfold_projs at h
      simp only [ZFSet.qrel] at h
      dsimp only
      have hb2 : 0 < b * b := by
        rcases lt_trichotomy b 0 with hb' | hb' | hb'
        · exact ZFInt.mul_neg_neg_pos b b hb' hb'
        · exact absurd hb' hb
        · exact ZFInt.mul_pos_pos_pos b b hb' hb'
      have hd2 : 0 < d * d := by
        rcases lt_trichotomy d 0 with hd' | hd' | hd'
        · exact ZFInt.mul_neg_neg_pos d d hd' hd'
        · exact absurd hd' hd
        · exact ZFInt.mul_pos_pos_pos d d hd' hd'
      have key : (a * b) * (d * d) = (b * b) * (c * d) := by
        ac_change (a * d) * (b * d) = (b * c) * (b * d)
        rw [h]
      apply propext
      constructor
      · intro hab
        have h1 : 0 < (a * b) * (d * d) := ZFInt.mul_pos_pos_pos _ _ hab hd2
        rw [key] at h1
        exact ZFInt.pos_of_mul_pos h1 hb2
      · intro hcd
        have h1 : 0 < (b * b) * (c * d) := ZFInt.mul_pos_pos_pos _ _ hb2 hcd
        rw [←key, ZFInt.mul_comm (a * b) (d * d)] at h1
        exact ZFInt.pos_of_mul_pos h1 hd2

def lt (x y : ZFRat) : Prop := isPos (y - x)

instance : LT ZFRat where lt := lt
instance : LE ZFRat where le x y := x < y ∨ x = y

theorem isPos_eq (n : ZFInt × ZFInt') : isPos (mk n) ↔ 0 < n.1 * n.2 := Iff.rfl

theorem lt_eq (n m : ZFInt × ZFInt') :
    mk n < mk m ↔ 0 < (m.1 * n.2 - n.1 * m.2) * (m.2 * n.2) := by
  change isPos (mk m - mk n) ↔ _
  rw [sub_eq, isPos_eq]

theorem isPos_trichotomy (x : ZFRat) : isPos x ∨ x = 0 ∨ isPos (-x) := by
  induction x using Quotient.ind
  rename_i n
  obtain ⟨a, b, hb⟩ := n
  change isPos (mk (a, ⟨b, hb⟩)) ∨ mk (a, ⟨b, hb⟩) = 0 ∨ isPos (-mk (a, ⟨b, hb⟩))
  rw [isPos_eq, mk_eq_zero_iff, neg_eq, isPos_eq]
  rcases lt_trichotomy (a * b) 0 with h | h | h
  · right; right
    rw [←ZFInt.neg_mul_distrib]
    exact (ZFInt.neg_flip_lt (a * b)).mp h
  · right; left
    rw [ZFInt.mul_comm] at h
    exact ZFInt.mul_eq_zero_of_ne_zero h hb
  · left; exact h

theorem not_isPos_zero : ¬ isPos (0 : ZFRat) := by
  rw [zero_eq, isPos_eq]
  simp

theorem isPos_one : isPos (1 : ZFRat) := by
  rw [one_eq, isPos_eq]
  simp [ZFInt.zero_lt_one]

theorem isPos_add {x y : ZFRat} (hx : isPos x) (hy : isPos y) : isPos (x + y) := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  rename_i n m
  have hx' := (isPos_eq n).mp hx
  have hy' := (isPos_eq m).mp hy
  apply (isPos_eq _).mpr
  have hb2 : 0 < n.2.1 * n.2.1 := by
    rcases lt_trichotomy n.2.1 0 with hb | hb | hb
    · exact ZFInt.mul_neg_neg_pos _ _ hb hb
    · exact absurd hb n.2.2
    · exact ZFInt.mul_pos_pos_pos _ _ hb hb
  have hd2 : 0 < m.2.1 * m.2.1 := by
    rcases lt_trichotomy m.2.1 0 with hd | hd | hd
    · exact ZFInt.mul_neg_neg_pos _ _ hd hd
    · exact absurd hd m.2.2
    · exact ZFInt.mul_pos_pos_pos _ _ hd hd
  have key : (n.1 * m.2.1 + n.2.1 * m.1) * (n.2.1 * m.2.1) =
      (n.1 * n.2.1) * (m.2.1 * m.2.1) + (n.2.1 * n.2.1) * (m.1 * m.2.1) := by ring
  rw [key]
  exact add_pos (ZFInt.mul_pos_pos_pos _ _ hx' hd2) (ZFInt.mul_pos_pos_pos _ _ hb2 hy')

theorem isPos_mul {x y : ZFRat} (hx : isPos x) (hy : isPos y) : isPos (x * y) := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  rename_i n m
  have hx' := (isPos_eq n).mp hx
  have hy' := (isPos_eq m).mp hy
  apply (isPos_eq _).mpr
  have key : n.1 * m.1 * (n.2.1 * m.2.1) = (n.1 * n.2.1) * (m.1 * m.2.1) := by ring
  rw [key]
  exact ZFInt.mul_pos_pos_pos _ _ hx' hy'

theorem lt_irrefl (x : ZFRat) : ¬ x < x := by
  change ¬ isPos (x - x)
  rw [sub_self]
  exact not_isPos_zero

theorem not_isPos_and_isPos_neg {z : ZFRat} (h : isPos z) : ¬ isPos (-z) := by
  intro h'
  apply not_isPos_zero
  have := isPos_add h h'
  rwa [add_neg_cancel] at this

theorem lt_asymm {x y : ZFRat} (h : x < y) : ¬ y < x := by
  change isPos (y - x) at h
  change ¬ isPos (x - y)
  rw [show x - y = -(y - x) by ring]
  exact not_isPos_and_isPos_neg h

theorem lt_trans {x y z : ZFRat} (hxy : x < y) (hyz : y < z) : x < z := by
  change isPos (y - x) at hxy
  change isPos (z - y) at hyz
  change isPos (z - x)
  rw [show z - x = (y - x) + (z - y) by ring]
  exact isPos_add hxy hyz

theorem lt_trichotomy (x y : ZFRat) : x < y ∨ x = y ∨ y < x := by
  rcases isPos_trichotomy (y - x) with h | h | h
  · left; exact h
  · right; left; exact (sub_eq_zero.mp h).symm
  · right; right
    change isPos (x - y)
    rwa [neg_sub] at h

theorem le_refl (x : ZFRat) : x ≤ x := Or.inr rfl

theorem le_trans {x y z : ZFRat} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  rcases hxy with hxy | rfl
  · rcases hyz with hyz | rfl
    · exact Or.inl (lt_trans hxy hyz)
    · exact Or.inl hxy
  · exact hyz

theorem le_antisymm {x y : ZFRat} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  rcases hxy with hxy | rfl
  · rcases hyx with hyx | rfl
    · exact absurd hyx (lt_asymm hxy)
    · rfl
  · rfl

theorem le_total (x y : ZFRat) : x ≤ y ∨ y ≤ x := by
  rcases lt_trichotomy x y with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem lt_iff_le_not_ge (x y : ZFRat) : x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  constructor
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rintro (h' | rfl)
    · exact lt_asymm h h'
    · exact lt_irrefl _ h
  · rintro ⟨h | rfl, h2⟩
    · exact h
    · exact absurd (le_refl _) h2

noncomputable instance : LinearOrder ZFRat where
  le x y := x < y ∨ x = y
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable ((· ≤ ·) _ _)
  lt_iff_le_not_ge := lt_iff_le_not_ge

theorem add_le_add_left (a b : ZFRat) (h : a ≤ b) (c : ZFRat) : a + c ≤ b + c := by
  rcases h with h | rfl
  · refine Or.inl ?_
    change isPos (b - a) at h
    change isPos ((b + c) - (a + c))
    rwa [show (b + c) - (a + c) = b - a by ring]
  · exact Or.inr rfl

theorem zero_lt_one : (0 : ZFRat) < 1 := by
  change isPos (1 - 0)
  rw [sub_zero]
  exact isPos_one

theorem zero_le_one : (0 : ZFRat) ≤ 1 := Or.inl zero_lt_one

theorem mul_lt_mul_of_pos_left {a : ZFRat} (ha : 0 < a) {b c : ZFRat} (hbc : b < c) :
    a * b < a * c := by
  change isPos (a - 0) at ha
  rw [sub_zero] at ha
  change isPos (c - b) at hbc
  change isPos (a * c - a * b)
  rw [show a * c - a * b = a * (c - b) by ring]
  exact isPos_mul ha hbc

theorem mul_lt_mul_of_pos_right {a : ZFRat} (ha : 0 < a) {b c : ZFRat} (hbc : b < c) :
    b * a < c * a := by
  change isPos (a - 0) at ha
  rw [sub_zero] at ha
  change isPos (c - b) at hbc
  change isPos (c * a - b * a)
  rw [show c * a - b * a = (c - b) * a by ring]
  exact isPos_mul hbc ha

theorem mul_le_mul_of_nonneg_left {a : ZFRat} (ha : 0 ≤ a) {b c : ZFRat} (hbc : b ≤ c) :
    a * b ≤ a * c := by
  rcases ha with ha | rfl
  · rcases hbc with hbc | rfl
    · exact Or.inl (mul_lt_mul_of_pos_left ha hbc)
    · exact Or.inr rfl
  · simp

theorem mul_le_mul_of_nonneg_right {a : ZFRat} (ha : 0 ≤ a) {b c : ZFRat} (hbc : b ≤ c) :
    b * a ≤ c * a := by
  rcases ha with ha | rfl
  · rcases hbc with hbc | rfl
    · exact Or.inl (mul_lt_mul_of_pos_right ha hbc)
    · exact Or.inr rfl
  · simp

instance : IsOrderedRing ZFRat where
  add_le_add_left := add_le_add_left
  zero_le_one := zero_le_one
  mul_le_mul_of_nonneg_left _ ha _ _ hbc := mul_le_mul_of_nonneg_left ha hbc
  mul_le_mul_of_nonneg_right _ ha _ _ hbc := mul_le_mul_of_nonneg_right ha hbc

instance : PosMulStrictMono ZFRat where
  mul_lt_mul_of_pos_left _ ha _ _ hbc := mul_lt_mul_of_pos_left ha hbc

instance : MulPosStrictMono ZFRat where
  mul_lt_mul_of_pos_right _ ha _ _ hbc := mul_lt_mul_of_pos_right ha hbc

end Order

end Arithmetic
/-! ## Transfer to `ℚ`

`ZFRat` and `ℚ` are the same field: the ring morphism `ℚ →+* ZFRat` given by the `RatCast`
instance is injective because `ZFRat` has characteristic zero, and surjective because every
`mk (a, b)` is the quotient of the images of two integers. The resulting equivalence is
registered as a `TransferEquiv`, so that the `transfer` tactic reads a goal about `ZFRat` in `ℚ`:

```
example (x y : ZFRat) : x + y = y + x := by
  transfer ZFRat → ℚ =>
    rw [add_comm]
```

The field operations, the numerals and the casts travel through the generic `map_…` lemmas of
the `transfer_simps` simp set; the order relations are tagged below.
-/

section Transfer

instance instCharZero : CharZero ZFRat := AddMonoidWithOne.toCharZero

private theorem ratCast_surjective : Function.Surjective ((↑) : ℚ → ZFRat) := by
  intro x
  induction x using Quotient.ind with
  | _ x =>
    obtain ⟨a, b⟩ := x
    refine ⟨(ZFInt.equivInt a : ℚ) / (ZFInt.equivInt b.val : ℚ), ?_⟩
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, intCast_eq_mk, intCast_eq_mk,
      ZFInt.intCast_equivInt, ZFInt.intCast_equivInt, ← mk_eq_div]
    rfl

/-- The canonical ring equivalence between the quotient construction `ZFRat` and Lean's `ℚ`. -/
noncomputable def equivRat : ZFRat ≃+* ℚ :=
  (RingEquiv.ofBijective (Rat.castHom ZFRat)
    ⟨Rat.cast_injective, ratCast_surjective⟩).symm

@[simp, transfer_simps high]
theorem equivRat_ratCast (q : ℚ) : equivRat (q : ZFRat) = q := by
  change equivRat (equivRat.symm q) = q
  exact equivRat.apply_symm_apply q

@[simp]
theorem ratCast_equivRat (x : ZFRat) : ((equivRat x : ℚ) : ZFRat) = x := by
  change equivRat.symm (equivRat x) = x
  exact equivRat.symm_apply_apply x

theorem equivRat_le (a b : ZFRat) : equivRat a ≤ equivRat b ↔ a ≤ b := by
  constructor <;> intro h
  · have h' : ((equivRat a : ℚ) : ZFRat) ≤ ((equivRat b : ℚ) : ZFRat) := Rat.cast_mono h
    rwa [ratCast_equivRat, ratCast_equivRat] at h'
  · rwa [← ratCast_equivRat a, ← ratCast_equivRat b, Rat.cast_strictMono.le_iff_le] at h

theorem equivRat_lt (a b : ZFRat) : equivRat a < equivRat b ↔ a < b := by
  rw [lt_iff_not_ge, lt_iff_not_ge, equivRat_le]

/-- Equivalence used by the `transfer` tactic to move goals between `ZFRat` and `ℚ`. -/
noncomputable instance : TransferEquiv ZFRat ℚ := ⟨equivRat.toEquiv⟩

attribute [transfer_simps ←] equivRat_le equivRat_lt

end Transfer

end ZFRat

/- The carrier set of Rat, which is equivalent to the carrier type of ZFRat -/
noncomputable def zf_qcarrier := Int.prod (Int \ {(0 : ZFInt).into.val} )
noncomputable def zf_qcarrier_equiv_qcarrier :
  zf_qcarrier ≃ ZFInt × ZFInt'  :=
  Equiv.trans (@ZFQuotient.equivZFProdProd Int (Int \ {(0 : ZFInt).into.val} )) <|
  Equiv.prodCongr ({
    toFun := ZFInt.outof
    invFun := ZFInt.into
    left_inv := ZFInt.into_outof
    right_inv := ZFInt.outof_into
  }) ({
    toFun := fun ⟨z, hz⟩ => ⟨ZFInt.outof ⟨z, sdiff_subset hz⟩, by
      have hz' := hz
      rw [mem_sdiff, mem_singleton] at hz
      obtain not_zero := hz.right
      intro this
      apply congr_arg ZFInt.into at this
      rw [ZFInt.into_outof, Subtype.ext_iff] at this
      exact not_zero this
    ⟩
    invFun := fun ⟨z, nz ⟩ => ⟨ZFInt.into z, by
      rw [mem_sdiff, mem_singleton]
      exists (ZFInt.into z).prop
      intro h
      rw [←Subtype.ext_iff] at h
      apply ZFInt.into_inj at h
      exact nz h
    ⟩
    left_inv := by
      intro ⟨z, hz⟩
      dsimp only
      rw [Subtype.ext_iff]
      change ZFInt.into _ = z
      rw [ZFInt.into_outof]
    right_inv := by
      intro ⟨z, nz⟩
      rw [Subtype.ext_iff]
      dsimp only
      apply ZFInt.into_inj
      rw [ZFInt.into_outof, Subtype.ext_iff]
  })

/- The relation equivalence of Rat, which is equivalent to equivalence relation of ZFRat -/
open Classical in
@[expose]
noncomputable def zf_qrel : ZFSet := (zf_qcarrier.prod zf_qcarrier).sep fun pq =>
  if h : pq ∈ zf_qcarrier.prod zf_qcarrier then
    let h := mem_prod.mp h
    let pn : ZFInt := ZFInt.outof ⟨pq.π₁.π₁, by
      obtain ⟨p,hp, _,_, rfl⟩ := h
      rw [zf_qcarrier, mem_prod] at hp
      obtain ⟨pn, hpn, pd, hpd, rfl⟩ := hp
      rwa [π₁_pair,π₁_pair]
    ⟩
    let pd : ZFInt := ZFInt.outof ⟨pq.π₁.π₂, by
      obtain ⟨p,hp, _,_, rfl⟩ := h
      rw [zf_qcarrier, mem_prod] at hp
      obtain ⟨pn, hpn, pd, hpd, rfl⟩ := hp
      rw [π₁_pair,π₂_pair]
      exact sdiff_subset hpd
    ⟩
    let qn : ZFInt := ZFInt.outof ⟨pq.π₂.π₁, by
      obtain ⟨p,hp, q, hq, rfl⟩ := h
      rw [zf_qcarrier, mem_prod] at hq
      obtain ⟨pn, hpn, pd, hpd, rfl⟩ := hq
      rwa [π₂_pair,π₁_pair]
    ⟩
    let qd : ZFInt := ZFInt.outof ⟨pq.π₂.π₂, by
      obtain ⟨p,hp, q, hq, rfl⟩ := h
      rw [zf_qcarrier, mem_prod] at hq
      obtain ⟨pn, hpn, pd, hpd, rfl⟩ := hq
      rw [π₂_pair,π₂_pair]
      exact sdiff_subset hpd
    ⟩
    pn * qd = pd * qn
  else False

open Classical in
theorem zf_qrel_equiv_qrel :
    zf_qcarrier.equivZFRelation ⟨zf_qrel, sep_subset⟩ =
    (Function.onFun ZFSet.qrel zf_qcarrier_equiv_qcarrier) := by
  ext x y
  rw [equivZFRelation_related, Function.onFun, ZFSet.qrel]
  dsimp only
  rw [zf_qrel, mem_sep]
  conv =>
    enter [1, 1]
    discharge => rw [pair_mem_prod] ; exact ⟨x.prop, y.prop⟩
  rw [true_and, dif_pos <| pair_mem_prod.mpr ⟨x.prop, y.prop⟩]
  dsimp only
  rw [←propext_iff]
  congr <;> simp only [π₁_pair, π₂_pair]

theorem zf_qrel_eq : zf_qrel.is_rel_equivalence sep_subset :=  by
  apply zf_qcarrier.equivZFRelation_Equivalence ⟨zf_qrel, sep_subset⟩ |>.mp
  rw [zf_qrel_equiv_qrel]
  exact Equivalence.comap ZFSet.qrel_eq zf_qcarrier_equiv_qcarrier.toFun

/- The set of Rational numbers -/
noncomputable def Rat : ZFSet := Int.prod (Int \ {(0 : ZFInt).into.val} ) |>.ZFQuotient zf_qrel

noncomputable def equivRatZFRat : Rat ≃ ZFRat :=
  Equiv.trans
  (@ZFQuotient.equivZFQuotient zf_qcarrier zf_qrel sep_subset zf_qrel_eq)
  (Quotient.congr zf_qcarrier_equiv_qcarrier (by
    unfold ZFSet.instSetoidZFIntZFInt' ZFQuotient.toSetoid
    dsimp only
    intro x y
    rw [zf_qrel_equiv_qrel]
  ))

end Rationals
end ZFSet

end
