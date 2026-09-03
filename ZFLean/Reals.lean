/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo POUILLAT
-/
module

public import ZFLean.Rationals
public import ZFLean.Naturals
import ZFLean.Quotient
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Rat.Cast.Order

/-! # ZFC Real Numbers

This file defines the real numbers in ZFC, based on the Cauchy sequences of ZFRat.

-/

public section

namespace ZFSet

section Reals

namespace ZFReal.RQuot

/-! # Real numbers quotient structure

Definitions and theorems about the underlying structure of `Real`.
-/

/- Convenient theorem for extracting a common `N` such that for all `n > N` both `p` and `q` are
  valid. -/
theorem exists_for_both {p q : ZFNat → Prop}
  (hp : ∃ N, ∀ n, N < n → p n)
  (hq : ∃ N, ∀ n, N < n → q n) :
    ∃ N, ∀ n, N < n → p n ∧ q n := by
  have ⟨Np, hp⟩ := hp
  have ⟨Nq, hq⟩ := hq
  exists max Np Nq
  intro n nb
  constructor
  · exact hp n <| lt_of_le_of_lt Std.left_le_max nb
  · exact hq n <| lt_of_le_of_lt Std.right_le_max nb

theorem exists_for_both₂ {p q : ZFNat → ZFNat → Prop}
  (hp : ∃ N, ∀ n m, N < n → N < m → p n m)
  (hq : ∃ N, ∀ n m, N < n → N < m → q n m) :
    ∃ N, ∀ n m, N < n → N < m → p n m ∧ q n m := by
  have ⟨Np, hp⟩ := hp
  have ⟨Nq, hq⟩ := hq
  exists max Np Nq
  intro n m nb mb
  constructor
  · apply hp n m <;> apply lt_of_le_of_lt (le_max_left Np Nq) <;> assumption
  · apply hq n m <;> apply lt_of_le_of_lt (le_max_right Np Nq) <;> assumption

abbrev isCauchy.{u} (u : ZFNat → ZFRat.{u}) :=
    ∀ e : ZFRat, 0 < e → ∃ N, ∀ n m, N < n → N < m → |u n - u m| < e

theorem Bounded_of_isCauchy {u : ZFNat → ZFRat} (h : isCauchy.{u} u) (d : ZFRat.{u}) (dp : 0 < d) :
    ∃ N, ∀ n, N < n → |u n| < |u (N + 1)| + d := by
  obtain ⟨N, h⟩:= h d dp
  exists N
  intro n nb
  specialize h n (N+1) nb (ZFNat.add_one_eq_succ ▸ ZFNat.lt_succ)
  apply lt_add_of_sub_left_lt
  apply lt_of_le_of_lt (abs_sub_abs_le_abs_sub _ _) h

noncomputable abbrev carrier := funs Nat Rat |>.sep fun a =>
  open Classical in
  if h : a ∈ funs Nat Rat then
    let a (n : ZFNat) : ZFRat := equivRatZFRat <| fapply a (is_func_is_pfunc <| mem_funs.mp h)
      ⟨n.val, by rw [is_func_dom_eq] ; exact n.prop⟩
    isCauchy a
  else False

@[zfun]
theorem is_func_of_carrier (a : carrier) : Nat.IsFunc Rat a.val :=
  mem_funs.mp <| And.left <| mem_sep.mp a.prop

@[zdom]
theorem mem_dom_of_carrier (a : carrier) (n : ZFNat) : n.val ∈ Dom a := by
  rw [is_func_dom_eq]
  exact n.prop

noncomputable instance instFunlike_zf_rcarrier : FunLike carrier ZFNat ZFRat where
  coe a n := equivRatZFRat <| @fapply a Nat Rat
      (is_func_is_pfunc <| is_func_of_carrier a) ⟨n.val, by rw [is_func_dom_eq] ; exact n.prop⟩
  coe_injective := by
    intro a b h
    apply Subtype.ext
    rw [funext_iff, Subtype.forall] at h
    dsimp only at h
    rw [ZFSet.is_func_ext_iff (is_func_of_carrier a) (is_func_of_carrier b)]
    intro n hn
    apply equivRatZFRat.injective
    exact h n hn

def rel (a b : carrier) : Prop :=
  ∀ e : ZFRat, 0 < e → ∃ N : ZFNat, ∀ n : ZFNat, N < n → |a n - b n| < e

theorem rel_equivalence : Equivalence rel where
  refl a := fun e pe => ⟨0,
    fun n nb =>  sub_self (a n) ▸ (@abs_zero ZFRat).symm ▸  pe⟩
  symm := @fun a b h e pe =>
    let ⟨N, hN⟩ := h e pe
    ⟨N, fun n nb => abs_sub_comm (a n) (b n) ▸ hN n nb⟩
  trans := by
    intro a b c hab hbc e pe
    have ⟨N, hN⟩  := exists_for_both
      (hab (e / 2) (div_pos pe two_pos)) (hbc (e / 2) (div_pos pe two_pos))
    exists N
    intro n nb
    specialize hN n nb
    conv =>
      congr
      · arg 1
        rw [←add_neg_cancel_right (a n) (- b n), neg_neg, add_sub_assoc,
          ←sub_eq_add_neg]
      · rw [←add_halves e]
    apply lt_of_le_of_lt (abs_add_le _ _)
    exact add_lt_add hN.left hN.right

noncomputable def zf_rel := carrier.equivZFRelation.symm rel

theorem zf_rel_equiv : zf_rel.val.is_rel_equivalence zf_rel.prop := by
  rw [←carrier.equivZFRelation_Equivalence, zf_rel, Equiv.apply_symm_apply]
  exact rel_equivalence

end ZFReal.RQuot

open ZFReal.RQuot

noncomputable abbrev Real := carrier.ZFQuotient zf_rel

noncomputable abbrev ZFReal : Type _ := Real
namespace ZFReal

namespace RQuot
/-!
Some of the ZFQuotient definitions/lemmas are specialized in order to avoid repeating boilerplate.
-/

noncomputable def class_of (a : carrier) : ZFReal :=
  ZFQuotient.class_of zf_rel.prop zf_rel_equiv a

theorem class_eq_iff_related (a b : carrier) :
    class_of a = class_of b ↔ rel a b := by
  rw [class_of, class_of, ZFQuotient.class_eq_iff_related zf_rel.prop zf_rel_equiv a b,
    ←carrier.equivZFRelation_related, zf_rel, Equiv.apply_symm_apply]

noncomputable def of_in_class {a : ZFReal} (u : a.val) : carrier := ZFQuotient.of_in_class  u

theorem class_of_mem_eq_self {a : ZFReal} (u : a.val) :
  class_of (of_in_class u) = a := ZFQuotient.class_of_mem_eq_self zf_rel.prop zf_rel_equiv a u

/-!
Some definitions to allow easier interoperability between ZFC Cauchy sequences and Lean functions.
-/

noncomputable def lambda_cauchy (u : ZFNat → ZFRat) (h : isCauchy u) : carrier :=
  ⟨λᶻ: Nat → Rat | hn : n => equivRatZFRat.symm (u ⟨n, hn⟩), by
    rw [mem_sep, and_iff_left_of_imp]
    · rw [mem_funs]
      apply lambda_isFunc
      intro x hx
      rw [dif_pos hx]
      exact SetLike.coe_mem (equivRatZFRat.symm (u ⟨x, hx⟩))
    intro hc
    rw [dif_pos hc, isCauchy]
    conv =>
      enter [e, 2, 1, N, n, m, 2, 2, 1, 1]
      congr <;>
      · rw [fapply_lambda' (by
            intro i hi
            rw [dif_pos hi]
            exact (equivRatZFRat.symm (u ⟨i, hi⟩)).prop
          ) <| Subtype.prop _]
        conv => enter [2,1] ; rw [dif_pos <| Subtype.prop _]
        rw [Subtype.eta, Equiv.apply_symm_apply, Subtype.eta]
    exact h
  ⟩

theorem lambda_cauchy_related {u v : ZFNat → ZFRat} (hu : isCauchy u) (hv : isCauchy v) :
      rel (lambda_cauchy u hu) (lambda_cauchy v hv)
    ↔ ∀ e : ZFRat, e > 0 → ∃ N, ∀ n, N < n → |u n - v n| < e := by
  rw [rel, lambda_cauchy, lambda_cauchy]
  conv =>
    enter [1, e, 2, 1, N, n, 2, 1, 1]
    rw [DFunLike.coe, instFunlike_zf_rcarrier]
    dsimp only
    congr <;>
    · rw [fapply_lambda' (by
        intro i hi
        rw [dif_pos hi]
        exact SetLike.coe_mem (equivRatZFRat.symm (_))
      ) n.prop]
      conv => enter [2,1] ; rw [dif_pos n.prop]
      rw [Subtype.eta, Equiv.apply_symm_apply, Subtype.eta]

theorem apply_lambda_cauchy {u : ZFNat → ZFRat} {h : isCauchy u} (n : ZFNat) :
    lambda_cauchy u h n = u n := by
  unfold lambda_cauchy
  rw [DFunLike.coe, instFunlike_zf_rcarrier]
  dsimp only
  conv =>
    enter [1, 2]
    rw [fapply_lambda' (by
        intro i hi
        rw [dif_pos hi]
        exact SetLike.coe_mem (equivRatZFRat.symm (_))
      ) n.prop]
    arg 1
    rw [dif_pos n.prop]
  rw [Subtype.eta, Equiv.apply_symm_apply]

noncomputable def lift₂ (f : carrier → carrier → α) (a b : Real) : α :=
  ZFQuotient.lift₂ f a b

theorem lift₂_class_of (f : carrier → carrier → α)
  (h : ∀ a b c d, rel a b → rel c d → f a c = f b d) (x y : carrier) :
  lift₂ f (class_of x) (class_of y) = f x y := by
  rw [lift₂, class_of, class_of]
  apply ZFQuotient.lift₂_class_of
  intro a b c d
  simp_rw [←carrier.equivZFRelation_related, zf_rel, Equiv.apply_symm_apply]
  exact h a b c d

noncomputable def map (f : carrier → carrier)
  (h : ∀ a b, rel a b → rel (f a) (f b)) : ZFReal → ZFReal :=
  ZFQuotient.map zf_rel.prop zf_rel_equiv f (by
    intro a b
    simp_rw [←carrier.equivZFRelation_related,  zf_rel, Equiv.apply_symm_apply]
    exact h a b
  )

theorem map_class_of (f : carrier → carrier)
  (h : ∀ a b, rel a b → rel (f a) (f b)) (u : carrier) :
    map f h (class_of u) = class_of (f u) := by
  rw [map, class_of, class_of]
  apply ZFQuotient.map_class_of

noncomputable def map₂ (f : carrier → carrier → carrier)
  (h : ∀ a b c d, rel a b → rel c d → rel (f a c) (f b d)) : ZFReal → ZFReal → ZFReal :=
  ZFQuotient.map₂ zf_rel.prop zf_rel_equiv f (by
    intro a b c d
    simp_rw [←carrier.equivZFRelation_related,  zf_rel, Equiv.apply_symm_apply]
    exact h a b c d
  )

theorem map₂_class_of (f : carrier → carrier → carrier)
  (h : ∀ a b c d, rel a b → rel c d → rel (f a c) (f b d)) (u v : carrier) :
    map₂ f h (class_of u) (class_of v) = class_of (f u v) := by
  rw [map₂, class_of, class_of, class_of]
  apply ZFQuotient.map₂_class_of

theorem isCauchy_of_carrier (u : carrier) : isCauchy ⇑u := by
  have h := u.prop
  rw [mem_sep] at h
  obtain ⟨hf, hc⟩ := h
  rw [dif_pos hf] at hc
  exact hc

noncomputable abbrev carrier_ofRat (q : Rat) : carrier :=
lambda_cauchy (fun _ => equivRatZFRat q) (by
    intro e ep
    exists 0
    intro n m nb mb
    dsimp only
    rw [sub_self, abs_zero]
    exact ep
  )

/-!
Some lemmas about Cauchy sequences.
-/

lemma eq_zero_of_eq_zero_of_related {a b : carrier} (related : rel a b)
  (h : ∀ e, 0 < e → ∃ N, ∀ n, N < n → |a n| < e) : ∀ e, 0 < e → ∃ N, ∀ n, N < n → |b n| < e := by
  intro e ep
  have ⟨N, hN⟩ := exists_for_both
    (h (e / 2) (div_pos ep two_pos)) (related (e / 2) (div_pos ep two_pos))
  exists N
  intro n np
  specialize hN n np
  obtain ⟨hB, hC⟩ := hN
  rw [←sub_zero (b n), abs_sub_comm, ←add_halves e]
  apply lt_of_le_of_lt (abs_sub_le _ (a n) _)
  rw [abs_sub_comm, sub_zero]
  exact Right.add_lt_add hB hC

lemma eq_zero_iff_eq_zero_of_related {u v : carrier} (related : rel u v) :
    (∀ e, 0 < e → ∃ N, ∀ n, N < n → |u n| < e) ↔ ∀ e, 0 < e → ∃ N, ∀ n, N < n → |v n| < e := by
  constructor
  · exact eq_zero_of_eq_zero_of_related related
  · exact eq_zero_of_eq_zero_of_related (rel_equivalence.symm related)

lemma away_from_zero_of_not_zero {u : carrier} :
    ¬(∀ e, 0 < e → ∃ N, ∀ n, N < n → |u n| < e) → ∃ s, 0 < s ∧ ∃ N, ∀ n > N, s < |u n| := by
  push Not
  rintro ⟨s, sp, hs⟩
  have ⟨N, hN⟩ := (isCauchy_of_carrier u) (s / 2) (div_pos sp two_pos)
  exists (s / 2), (div_pos sp two_pos)
  specialize hs N
  obtain ⟨m, mb, hm⟩ := hs
  exists N
  intro n nb
  specialize hN n m nb mb
  rw [←neg_lt_neg_iff]
  apply lt_of_add_lt_add_left
  refine add_lt_of_add_lt_right ?_ hm
  rw [←sub_eq_add_neg,←sub_eq_add_neg, sub_half]
  apply lt_of_le_of_lt
  · exact abs_sub_abs_le_abs_sub (u m) (u n)
  · rw [abs_sub_comm]
    exact hN

end RQuot

/- An embedding from `Rat` to `Real`. To transfer an operation look for `ofRat_*`. -/
noncomputable def ofRat (q : Rat) : ZFReal :=
  class_of <| lambda_cauchy (fun _ => equivRatZFRat q) (by
    intro e ep
    exists 0
    intro n m nb mb
    dsimp only
    rw [sub_self, abs_zero]
    exact ep
  )

-- assert definition coherence
example (q : Rat) : ofRat q = class_of (carrier_ofRat q) := rfl

theorem ofRat_inj : Function.Injective ofRat := by
  intro p q
  rw [ofRat, ofRat, class_eq_iff_related, lambda_cauchy_related]
  intro h
  apply equivRatZFRat.injective
  set p := equivRatZFRat p
  set q := equivRatZFRat q
  rw [←sub_eq_zero, ZFRat.separation]
  intro e ep
  obtain ⟨N, h⟩ := h e ep
  exact h (N.succ) ZFNat.lt_succ

noncomputable def natCast : ℕ → ZFReal := (ofRat <| equivRatZFRat.symm ·)
noncomputable instance : NatCast ZFReal where
  natCast := natCast
lemma natCast_def (q : ℕ) : (q : ℕ) = natCast q := rfl

noncomputable def intCast : ℤ → ZFReal := (ofRat <| equivRatZFRat.symm ·)
noncomputable instance : IntCast ZFReal where
  intCast := intCast
lemma intCast_def (q : ℤ) : (q : ℤ) = intCast q := rfl

noncomputable def ratCast : ℚ → ZFReal := (ofRat <| equivRatZFRat.symm ·)
noncomputable instance : RatCast ZFReal where
  ratCast := ratCast
lemma ratCast_def (q : ℚ) : (q : ℚ) = ratCast q := rfl

noncomputable def zero := ofRat (equivRatZFRat.symm 0)
noncomputable instance : Zero ZFReal where  zero := zero
lemma zero_def : 0 = zero := rfl
lemma ofRat_zero : ofRat (equivRatZFRat.symm 0) = 0 := zero_def

noncomputable def one := ofRat (equivRatZFRat.symm 1)
noncomputable instance : One ZFReal where one := one
lemma one_def : 1 = one := rfl
lemma ofRat_one : ofRat (equivRatZFRat.symm 1) = 1 := one_def

noncomputable def add := map₂
  (fun u v => lambda_cauchy (fun n => u n + v n) (by
    intro e ep
    obtain ⟨N, hN⟩ := exists_for_both₂
      (isCauchy_of_carrier u (e / 2) (div_pos ep two_pos))
      (isCauchy_of_carrier v (e / 2) (div_pos ep two_pos))
    exists N
    intro n m nb mb
    specialize hN n m nb mb
    rw [add_sub_add_comm,← add_halves e]
    apply lt_of_le_of_lt (abs_add_le _ _)
    exact add_lt_add hN.left hN.right
  )) (by
    intro a b c d hab hcd
    rw [lambda_cauchy_related]
    intro e ep
    obtain ⟨N, hN⟩ := exists_for_both
      (hab (e / 2) (div_pos ep two_pos))
      (hcd (e / 2) (div_pos ep two_pos))
    exists N
    intro n nb
    specialize hN n nb
    rw [add_sub_add_comm,← add_halves e]
    apply lt_of_le_of_lt (abs_add_le _ _)
    apply add_lt_add hN.left hN.right
  )
noncomputable instance : Add ZFReal where add := add
lemma add_def (a b : ZFReal) : a + b = add a b := rfl
theorem ofRat_add (p q : ZFRat) : ofRat (equivRatZFRat.symm (p + q)) =
    ofRat (equivRatZFRat.symm (p)) + ofRat (equivRatZFRat.symm (q)) := by
  simp_rw [add_def, add, ofRat, map₂_class_of, apply_lambda_cauchy, Equiv.apply_symm_apply]

noncomputable def mul : ZFReal → ZFReal → ZFReal := map₂
  (fun u v => lambda_cauchy (fun n => u n * v n) (by
    intro e ep
    dsimp only
    have huC := isCauchy_of_carrier u
    have ⟨NuB , huB⟩ := Bounded_of_isCauchy huC 1 one_pos
    have hvC := isCauchy_of_carrier v
    have ⟨NvB , hvB⟩ := Bounded_of_isCauchy hvC 1 one_pos
    have ⟨NuC , huC⟩ := huC ((e / 2) / (|v (NvB + 1)| + 1)) (div_pos (div_pos ep two_pos)
      (add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos))
    have ⟨NvC , hvC⟩ := hvC ((e / 2) / (|u (NuB + 1)| + 1)) (div_pos (div_pos ep two_pos)
      (add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos))
    have hu := exists_for_both₂ ⟨NuB, fun n m nb mb => huB n nb⟩ ⟨NuC, huC⟩
    have hv := exists_for_both₂ ⟨NvB, fun n m nb mb => hvB m mb⟩ ⟨NvC, hvC⟩
    obtain ⟨N, hN⟩ :=  exists_for_both₂ hu hv
    exists N
    intro n m nb mb
    specialize hN n m nb mb
    rw [sub_eq_add_neg,←add_neg_add_add_cancel _ (u n * v m), ←sub_eq_add_neg, ←sub_eq_add_neg,
      ←mul_sub_left_distrib, ←mul_sub_right_distrib, ← add_halves e]
    apply lt_of_le_of_lt (abs_add_le _ _)
    rw [abs_mul, abs_mul]
    apply add_lt_add
    · if h : u n = 0 then
        rw [h, abs_zero, zero_mul]
        exact div_pos ep two_pos
      else
      rw [← mul_inv_cancel_left₀ (Ne.symm <| ne_of_lt <| add_pos_of_nonneg_of_pos
        (abs_nonneg (u (NuB + 1))) one_pos) (e / 2)]
      conv => congr <;> rw [mul_comm]
      apply mul_lt_mul
      · rw [mul_comm, ←Field.div_eq_mul_inv]
        exact hN.right.right
      · apply le_of_lt
        exact hN.left.left
      · rw [abs_pos, ne_eq]
        exact h
      · refine le_of_lt (mul_pos ?_ (div_pos ep two_pos))
        · rw [inv_pos]
          exact add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos
    · rw [mul_comm]
      if h : v m = 0 then
        rw [h, abs_zero, zero_mul]
        exact div_pos ep two_pos
      else
      rw [← mul_inv_cancel_left₀ (Ne.symm <| ne_of_lt <| add_pos_of_nonneg_of_pos
        (abs_nonneg (v (NvB + 1))) one_pos) (e / 2)]
      conv => congr <;> rw [mul_comm]
      apply mul_lt_mul
      · rw [mul_comm, ←Field.div_eq_mul_inv]
        exact hN.left.right
      · apply le_of_lt
        exact hN.right.left
      · rw [abs_pos, ne_eq]
        exact h
      · refine le_of_lt (mul_pos ?_ (div_pos ep two_pos))
        · rw [inv_pos]
          exact add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos
  )) (by
    intro a b c d hab hcd
    rw [lambda_cauchy_related]
    intro e ep
    have huC := isCauchy_of_carrier a
    have ⟨NuB , huB⟩ := Bounded_of_isCauchy huC 1 one_pos
    have hvC := isCauchy_of_carrier d
    have ⟨NvB , hvB⟩ := Bounded_of_isCauchy hvC 1 one_pos
    have ⟨NuC , huC⟩ := hab ((e / 2) / (|d (NvB + 1)| + 1)) (div_pos (div_pos ep two_pos)
      (add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos))
    have ⟨NvC , hvC⟩ := hcd ((e / 2) / (|a (NuB + 1)| + 1)) (div_pos (div_pos ep two_pos)
      (add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos))
    have hu := exists_for_both ⟨NuB, huB⟩ ⟨NuC, huC⟩
    have hv := exists_for_both ⟨NvB, hvB⟩ ⟨NvC, hvC⟩
    obtain ⟨N, hN⟩ :=  exists_for_both hu hv
    exists N
    intro n nb
    specialize hN n nb
    rw [sub_eq_add_neg,←add_neg_add_add_cancel _ (a n * d n), ←sub_eq_add_neg, ←sub_eq_add_neg,
      ←mul_sub_left_distrib, ←mul_sub_right_distrib, ← add_halves e]
    apply lt_of_le_of_lt (abs_add_le _ _)
    rw [abs_mul, abs_mul]
    apply add_lt_add
    · if h : a n = 0 then
        rw [h, abs_zero, zero_mul]
        exact div_pos ep two_pos
      else
      rw [← mul_inv_cancel_left₀ (Ne.symm <| ne_of_lt <| add_pos_of_nonneg_of_pos
        (abs_nonneg (a (NuB + 1))) one_pos) (e / 2)]
      conv => congr <;> rw [mul_comm]
      apply mul_lt_mul
      · rw [mul_comm, ←Field.div_eq_mul_inv]
        exact hN.right.right
      · apply le_of_lt
        exact hN.left.left
      · rw [abs_pos, ne_eq]
        exact h
      · refine le_of_lt (mul_pos ?_ (div_pos ep two_pos))
        · rw [inv_pos]
          exact add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos
    · rw [mul_comm]
      if h : d n = 0 then
        rw [h, abs_zero, zero_mul]
        exact div_pos ep two_pos
      else
      conv =>
        right
        rw [← mul_inv_cancel_left₀ (Ne.symm <| ne_of_lt <| add_pos_of_nonneg_of_pos
          (abs_nonneg (d (NvB + 1))) one_pos) (e / 2)]
      conv => congr <;> rw [mul_comm]
      apply mul_lt_mul
      · rw [mul_comm, ←Field.div_eq_mul_inv]
        exact hN.left.right
      · apply le_of_lt
        exact hN.right.left
      · rw [abs_pos, ne_eq]
        exact h
      · refine le_of_lt (mul_pos ?_ (div_pos ep two_pos))
        · rw [inv_pos]
          exact add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos
  )
noncomputable instance : Mul ZFReal where mul := mul
lemma mul_def (a b : ZFReal) : a * b = mul a b := rfl
theorem ofRat_mul (p q : ZFRat) : ofRat (equivRatZFRat.symm (p * q)) =
    ofRat (equivRatZFRat.symm (p)) * ofRat (equivRatZFRat.symm (q)) := by
  simp_rw [mul_def, mul, ofRat, map₂_class_of, apply_lambda_cauchy, Equiv.apply_symm_apply]

noncomputable def neg (a : ZFReal) := ofRat (equivRatZFRat.symm (-1)) * a
noncomputable instance : Neg ZFReal where neg := neg
lemma neg_def (a : ZFReal) : -a = neg a := rfl
theorem ofRat_neg (p : ZFRat) :
    ofRat (equivRatZFRat.symm (-p)) = - ofRat (equivRatZFRat.symm (p)) := by
  rw [neg_def, neg, mul_def, mul, ofRat, ofRat, ofRat, map₂_class_of]
  congr
  ext x
  simp_rw [apply_lambda_cauchy, Equiv.apply_symm_apply]
  exact neg_eq_neg_one_mul p

noncomputable def inv := RQuot.map
  (fun u =>
    open Classical in
    if h : ∀ e, 0 < e → ∃ N, ∀ n, N < n → |u n| < e then
      of_in_class <| ZFQuotient.choose_repr 0
    else lambda_cauchy (fun n => (u n)⁻¹) (by
      have ⟨s, sp, Nz, hz⟩ := away_from_zero_of_not_zero h
      intro e ep
      have ⟨N, hN⟩ := exists_for_both₂
        (isCauchy_of_carrier u (e * (s * s)) (mul_pos ep <| mul_pos sp sp))
        ⟨Nz, fun n m nb mb => And.intro (hz n nb) (hz m mb)⟩
      exists N
      intro n m nb mb
      specialize hN n m nb mb
      obtain ⟨hC,hz⟩ := hN
      have hzn := lt_trans sp hz.left
      have hzm := lt_trans sp hz.right
      conv at hz =>
        rw [←inv_lt_inv₀ hzn sp, ←inv_lt_inv₀ hzm sp]
        congr <;> rw [←ZFRat.abs_inv]
      replace hz := mul_lt_mul'' hz.left hz.right (abs_nonneg _) (abs_nonneg _)
      conv at hz =>
        rw [←abs_mul, ←mul_inv, ←mul_inv]
      rw [inv_sub_inv
          (abs_ne_zero.mp <| Ne.symm <| ne_of_lt <| hzn)
          (abs_ne_zero.mp <| Ne.symm <| ne_of_lt <| hzm),
        div_eq_inv_mul, abs_mul, mul_comm]
      rw [←mul_one e,
        ←Field.mul_inv_cancel _ (mul_self_ne_zero.mpr (Ne.symm <| ne_of_lt sp))]
      rw [←mul_assoc, abs_sub_comm]
      exact mul_lt_mul'' hC hz (abs_nonneg _) (abs_nonneg _)
    )) (by
      intro u v related
      have he := eq_zero_iff_eq_zero_of_related related
      if h : ∀ e, 0 < e → ∃ N, ∀ n, N < n → |u n| < e then
        rw [dif_pos h, dif_pos <| he.mp h]
        exact rel_equivalence.refl _
      else
      rw [dif_neg h, dif_neg <| he.not.mp h, lambda_cauchy_related]
      have ⟨u_s, u_sp, uz⟩ := away_from_zero_of_not_zero h
      have ⟨v_s, v_sp, vz⟩ := away_from_zero_of_not_zero <| he.not.mp h
      intro e ep
      have ⟨N, hN⟩ := exists_for_both (related (e * (v_s * u_s)) (mul_pos ep <| mul_pos v_sp u_sp))
        <| exists_for_both uz vz
      exists N
      intro n nb
      specialize hN n nb
      obtain ⟨hC,hz⟩ := hN
      have hzn := lt_trans u_sp hz.left
      have hzm := lt_trans v_sp hz.right
      conv at hz =>
        rw [←inv_lt_inv₀ hzn u_sp, ←inv_lt_inv₀ hzm v_sp]
        congr <;> rw [←ZFRat.abs_inv]
      replace hz := mul_lt_mul'' hz.left hz.right (abs_nonneg _) (abs_nonneg _)
      conv at hz =>
        rw [←abs_mul, ←mul_inv, ←mul_inv]
        right ; rw [mul_comm]
      rw [inv_sub_inv
          (abs_ne_zero.mp <| Ne.symm <| ne_of_lt <| hzn)
          (abs_ne_zero.mp <| Ne.symm <| ne_of_lt <| hzm),
        div_eq_inv_mul, abs_mul, mul_comm]
      rw [←mul_one e,
        ←Field.mul_inv_cancel _ (Ne.symm <| ne_of_lt <| mul_pos v_sp u_sp)]
      rw [←mul_assoc, abs_sub_comm]
      exact mul_lt_mul'' hC hz (abs_nonneg _) (abs_nonneg _)
    )
noncomputable instance (priority := high) : Inv ZFReal where inv := inv
lemma inv_def (a : ZFReal) : Inv.inv a = inv a := rfl
theorem ofRat_inv (p : ZFRat) :
    ofRat (equivRatZFRat.symm (p⁻¹)) = Inv.inv (ofRat (equivRatZFRat.symm (p))) := by
  rw [inv_def, inv, ofRat, ofRat, map_class_of]
  split_ifs with h
  · conv at h =>
      enter [e, ep, 1, N, n]
      rw [apply_lambda_cauchy, Equiv.apply_symm_apply]
    have z : p = 0 := by
      rw [ZFRat.separation]
      intro e ep
      specialize h e ep
      obtain ⟨N, h⟩ := h
      exact h (ZFNat.succ N) ZFNat.lt_succ
    trans class_of (carrier_ofRat (equivRatZFRat.symm 0))
    · congr
      ext
      rw [z, inv_zero]
    · rw [class_of_mem_eq_self, zero_def, zero, ofRat]
  · congr
    ext n
    simp_rw [apply_lambda_cauchy, Equiv.apply_symm_apply]

noncomputable instance : AddCommSemigroup ZFReal where
  add_comm a b := by
    have u := ZFQuotient.choose_repr a
    have v := ZFQuotient.choose_repr b
    conv => congr <;> rw [add_def, add]
    rw [←class_of_mem_eq_self u, ←class_of_mem_eq_self v, map₂_class_of, map₂_class_of]
    conv => enter [1, 1, 1, n] ; rw [add_comm]
  add_assoc a b c := by
    have u := ZFQuotient.choose_repr a
    have v := ZFQuotient.choose_repr b
    have w := ZFQuotient.choose_repr c
    simp_rw [add_def, add]
    rw [←class_of_mem_eq_self u, ←class_of_mem_eq_self v, ←class_of_mem_eq_self w]
    simp_rw [map₂_class_of, apply_lambda_cauchy, add_assoc]

noncomputable instance : CommSemigroup ZFReal where
  mul_comm a b := by
    have u := ZFQuotient.choose_repr a
    have v := ZFQuotient.choose_repr b
    conv => congr <;> rw [mul_def, mul]
    rw [←class_of_mem_eq_self u, ←class_of_mem_eq_self v, map₂_class_of, map₂_class_of]
    conv => enter [1, 1, 1, n] ; rw [mul_comm]
  mul_assoc a b c := by
      have u := ZFQuotient.choose_repr a
      have v := ZFQuotient.choose_repr b
      have w := ZFQuotient.choose_repr c
      simp_rw [mul_def, mul]
      rw [←class_of_mem_eq_self u, ←class_of_mem_eq_self v, ←class_of_mem_eq_self w]
      simp_rw [map₂_class_of, apply_lambda_cauchy, mul_assoc]

protected lemma add_zero (a : ZFReal) : a + 0 = a := by
    have u := ZFQuotient.choose_repr a
    rw [add_def, add, zero_def, zero, ←class_of_mem_eq_self u, ofRat, map₂_class_of]
    congr
    apply DFunLike.coe_injective
    ext x
    rw [apply_lambda_cauchy, apply_lambda_cauchy, Equiv.apply_symm_apply, add_zero]

protected lemma mul_zero (a : ZFReal) : a * 0 = 0 := by
    have u := ZFQuotient.choose_repr a
    rw [mul_def, mul, zero_def, zero, ←class_of_mem_eq_self u, ofRat, map₂_class_of]
    congr
    ext x
    rw [apply_lambda_cauchy, Equiv.apply_symm_apply, mul_zero]

protected lemma mul_one (a : ZFReal) : a * 1 = a := by
    have u := ZFQuotient.choose_repr a
    rw [mul_def, mul, one_def, one, ←class_of_mem_eq_self u, ofRat, map₂_class_of]
    congr
    apply DFunLike.coe_injective
    ext x
    simp_rw [apply_lambda_cauchy, Equiv.apply_symm_apply, mul_one]

noncomputable instance : AddZeroClass ZFReal where
  add_zero := ZFReal.add_zero
  zero_add a := add_comm a 0 ▸ ZFReal.add_zero a

noncomputable instance : MulZeroOneClass ZFReal where
  mul_zero := ZFReal.mul_zero
  zero_mul a := mul_comm a 0 ▸ ZFReal.mul_zero a
  mul_one := ZFReal.mul_one
  one_mul a := mul_comm a 1 ▸ ZFReal.mul_one a

protected lemma left_distrib (a b c : ZFReal) : a * (b + c) = a * b + a * c := by
    have u := ZFQuotient.choose_repr a
    have v := ZFQuotient.choose_repr b
    have w := ZFQuotient.choose_repr c
    simp_rw [add_def, add, mul_def, mul]
    rw [←class_of_mem_eq_self u, ←class_of_mem_eq_self v, ←class_of_mem_eq_self w]
    simp_rw [map₂_class_of, apply_lambda_cauchy]
    congr
    ext x
    apply left_distrib

noncomputable instance : Distrib ZFReal where
  left_distrib := ZFReal.left_distrib
  right_distrib a b c := by
    conv =>
      congr
      · rw [mul_comm]
      · congr <;> rw [mul_comm]
    rw [ZFReal.left_distrib]

noncomputable instance : HasDistribNeg ZFReal where
  neg_neg a := by
    rw [neg_def, neg, neg_def, neg, ←mul_assoc, ←ofRat_mul, neg_mul_neg, one_mul, ←one, ←one_def,
      one_mul]
  neg_mul a b := by
    rw [neg_def, neg, neg_def, neg, ←mul_assoc]
  mul_neg a b := by
    conv => congr <;> rw [mul_comm]
    rw [neg_def, neg, neg_def, neg, ←mul_assoc]

noncomputable instance : Field ZFReal where
  mul_zero := ZFReal.mul_zero
  zero_mul a := mul_comm a 0 ▸ ZFReal.mul_zero a
  mul_one := ZFReal.mul_one
  one_mul a := mul_comm a 1 ▸ ZFReal.mul_one a
  exists_pair_ne := by
    exists 0, 1
    rw [zero_def, zero, one_def, one]
    intro h
    apply ofRat_inj at h
    apply equivRatZFRat.symm.injective at h
    exact ne_of_lt ZFRat.zero_lt_one h
  inv_zero := by
    rw [zero_def, zero, inv_def, inv, ofRat, map_class_of, dif_pos]
    · rw [class_of_mem_eq_self, zero_def, zero, ofRat]
    · intro e ep
      exists 0
      intro n nb
      rw [apply_lambda_cauchy, Equiv.apply_symm_apply, abs_zero]
      exact ep
  mul_inv_cancel a anz := by
    have u := ZFQuotient.choose_repr a
    rw [←class_of_mem_eq_self u, zero_def, zero, ofRat, ne_eq, class_eq_iff_related] at anz
    simp_rw [Equiv.apply_symm_apply, rel, apply_lambda_cauchy, sub_zero] at anz
    rw [←class_of_mem_eq_self u, inv_def, inv, map_class_of, dif_neg anz, mul_def, mul,
      map₂_class_of, one_def, one, ofRat, class_eq_iff_related]
    intro e ep
    apply away_from_zero_of_not_zero at anz
    have ⟨s, sp, N, hN⟩ := anz
    exists N
    intro n nb
    specialize hN n nb
    rw [apply_lambda_cauchy, apply_lambda_cauchy, apply_lambda_cauchy, Equiv.apply_symm_apply,
      Field.mul_inv_cancel, sub_self, abs_zero]
    · exact ep
    · apply abs_ne_zero.mp
      apply Ne.symm <| ne_of_lt _
      trans s
      · exact sp
      · exact hN
  neg_add_cancel a := by
    have u := ZFQuotient.choose_repr a
    rw [neg_def, neg, mul_def, mul, add_def, add, zero_def, zero, ←class_of_mem_eq_self u]
    simp_rw [ofRat, map₂_class_of, apply_lambda_cauchy, Equiv.apply_symm_apply]
    congr
    ext x
    rw [neg_one_mul]
    apply neg_add_cancel
  nsmul n a := a * ofRat (equivRatZFRat.symm n)
  zsmul n a := a * ofRat (equivRatZFRat.symm n)
  nsmul_zero a := by
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [Nat.cast_zero, ←zero, ←zero_def]
    exact mul_zero a
  nsmul_succ n a := by
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [Nat.cast_add, Nat.cast_one, ofRat_add, left_distrib, ←one, ←one_def, mul_one]
  zsmul_zero' a := by
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [Int.cast_zero, ←zero, ←zero_def]
    exact mul_zero a
  zsmul_succ' z a := by
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [Nat.cast_succ, Int.cast_add, Int.cast_one, ofRat_add, left_distrib, ←one,
      ←one_def, mul_one]
  zsmul_neg' z a := by
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Int.negSucc_eq, Int.cast_neg,
      Int.cast_add, Int.cast_one, neg_add, ofRat_add, ofRat_add, ofRat_neg, ofRat_neg, ←mul_neg]
    congr
    simp_rw [neg_def, neg, left_distrib]
  qsmul q a := (ofRat <| equivRatZFRat.symm q) * a
  qsmul_def _ _ :=  by
    rw [ratCast_def, ratCast]
  ratCast_def q := by
    conv => left ; rw [←Rat.num_div_den q]
    simp_rw [ratCast_def, ratCast, intCast_def, intCast, natCast_def, natCast, Rat.cast_div,
      Rat.cast_intCast, Rat.cast_natCast, div_eq_mul_inv, ofRat_mul, ofRat_inv, HDiv.hDiv,
      DivInvMonoid.div']
  natCast_succ n := by
    simp_rw [NatCast.natCast, natCast, Nat.cast_add, Nat.cast_one, ofRat_add, one_def, one]
  natCast_zero := by
    simp_rw [NatCast.natCast, natCast, Nat.cast_zero, zero_def, zero]
  intCast_negSucc n := by
    simp_rw [IntCast.intCast, intCast, Int.cast_negSucc, ofRat_neg, natCast_def, natCast]
  nnqsmul := _

theorem RQuot.away_of_ne {u v : carrier} :
    ¬ rel u v → ∃ e, 0 < e ∧ ∃ N, ∀ n, N < n → e < |u n - v n| := by
  rw [rel]
  have (eq := hc) c := class_of u - class_of v
  rw [sub_eq_add_neg, neg_def, neg, ofRat, mul_def, mul, map₂_class_of, add_def, add,
    map₂_class_of] at hc
  conv at hc =>
    enter [2, 1, 1, n]
    rw [apply_lambda_cauchy, apply_lambda_cauchy, Equiv.apply_symm_apply, neg_mul, one_mul,
      ← sub_eq_add_neg]
  set w := lambda_cauchy (fun n => u n - v n) _ with hw
  have h := hw ▸ @away_from_zero_of_not_zero w
  conv at h =>
    congr
    · enter [1, e, ep, 1, N, n, nb]
      rw [apply_lambda_cauchy]
    · enter [1, s, 2, 1, N, n, nb]
      rw [apply_lambda_cauchy]
  exact h

noncomputable def lt (a b : ZFReal) : Prop :=
  lift₂ (fun u v => ∃ s, 0 < s ∧ ∃ N, ∀ n, N < n → u n + s < v n) a b
noncomputable instance instLT : LT ZFReal where lt := lt
lemma lt_def (a b : ZFReal) : (a < b) = lt a b := rfl
theorem RQuot.lt_class_of (u v : carrier) :
    (class_of u < class_of v) = ∃ s, 0 < s ∧ ∃ N, ∀ n, N < n → u n + s < v n := by
  rw [lt_def, lt, lift₂_class_of]
  simp_rw [propext_iff, iff_iff_implies_and_implies, forall_and]
  rw [and_iff_left_of_imp]
  · rintro a b c d ab_related cd_related ⟨s, sp, N, hN⟩
    exists s / 3, div_pos sp three_pos
    have ⟨N, hN⟩ := exists_for_both ⟨N, hN⟩ <|
      exists_for_both
      (ab_related (s / 3) (div_pos sp three_pos))
      (cd_related (s / 3) (div_pos sp three_pos))
    exists N
    intro n nb
    specialize hN n nb
    obtain ⟨h,hab, hcd⟩ := hN
    apply sub_lt_of_abs_sub_lt_left at hab
    rw [sub_lt_iff_lt_add, ←add_lt_add_iff_right (s / 3), add_assoc, ←add_div, ←two_mul] at hab
    apply sub_lt_of_abs_sub_lt_right at hcd
    rw [←mul_one s, ←Field.mul_inv_cancel 3 three_ne_zero, ←mul_assoc, ←div_eq_mul_inv, mul_comm,
      ←two_add_one_eq_three, right_distrib, one_mul, two_add_one_eq_three, add_div, ←add_assoc,
      ←add_lt_add_iff_right (-(s / 3)), add_assoc, add_neg_cancel, add_zero, ←sub_eq_add_neg] at h
    exact lt_trans hab <| lt_trans h hcd
  · intro h a b c d ab_related cd_related
    exact h b a d c (rel_equivalence.symm ab_related) (rel_equivalence.symm cd_related)
lemma ofRat_lt (p q : ZFRat) :
  (p < q) = (ofRat (equivRatZFRat.symm p) < ofRat (equivRatZFRat.symm q)) := by
  rw [propext_iff, ofRat, ofRat, lt_class_of]
  conv =>
    enter [2, 1, s, 2]
    conv =>
      enter [1, N]
      conv =>
        ext n
        conv => right ; congr <;> rw [apply_lambda_cauchy, Equiv.apply_symm_apply]
  constructor
  · intro h
    exists (q - p) / 2, div_pos (sub_pos_of_lt h) two_pos, 0
    intro n nb
    rw [lt_iff_exists_pos_add]
    exists (q - p) / 2, div_pos (sub_pos_of_lt h) two_pos
    rw [add_assoc, add_halves]
    exact add_sub_cancel p q
  · rintro ⟨s, sp, N, hN⟩
    specialize hN N.succ ZFNat.lt_succ
    apply lt_trans ((lt_add_iff_pos_right p).mpr sp) hN

protected lemma not_gt_of_lt {a b : ZFReal} : a < b → ¬ b < a := by
  have u := ZFQuotient.choose_repr a
  have v := ZFQuotient.choose_repr b
  rw [← class_of_mem_eq_self u,← class_of_mem_eq_self v, lt_class_of, lt_class_of]
  rintro ⟨s, sp, N, hN⟩ ⟨r, rp, M, hM⟩
  specialize hN (max N M |>.succ) (lt_of_le_of_lt (le_max_left N M) ZFNat.lt_succ)
  specialize hM (max N M |>.succ) (lt_of_le_of_lt (le_max_right N M) ZFNat.lt_succ)
  have h := add_lt_add hN hM
  rw [← sub_lt_sub_iff, add_sub_cancel_left, sub_add_cancel_left] at h
  exact not_lt_of_gt (lt_trans h (neg_neg_of_pos rp)) sp

protected lemma ne_of_lt {a b : ZFReal} : a < b → a ≠ b := by
  have u := ZFQuotient.choose_repr a
  have v := ZFQuotient.choose_repr b
  rw [← class_of_mem_eq_self u,← class_of_mem_eq_self v, lt_class_of, ne_eq, class_eq_iff_related]
  rintro ⟨s, sp, N, hN⟩
  intro h
  specialize h s sp
  obtain ⟨M, hM⟩ := h
  specialize hN (max N M |>.succ) (lt_of_le_of_lt (le_max_left N M) ZFNat.lt_succ)
  specialize hM (max N M |>.succ) (lt_of_le_of_lt (le_max_right N M) ZFNat.lt_succ)
  rw [abs_sub_comm, abs_sub_lt_iff] at hM
  apply And.left at hM
  rw [sub_lt_iff_lt_add] at hM
  apply lt_trans hN at hM
  rw [add_comm] at hM
  exact lt_irrefl _ hM

abbrev le (a b : ZFReal) : Prop := lt a b ∨ a = b
noncomputable instance (priority := default + 1) : LE ZFReal where le := le
lemma le_def (a b : ZFReal) : (a ≤ b) = le a b := rfl
lemma ofRat_le (p q : ZFRat) :
    (p ≤ q) = (ofRat (equivRatZFRat.symm p) ≤  ofRat (equivRatZFRat.symm q)) := by
  rw [le_def, le, ←lt_def, le_iff_lt_or_eq]
  congr 1
  · rw [ofRat_lt]
  · rw [ofRat_inj.eq_iff, equivRatZFRat.symm.injective.eq_iff]

noncomputable instance instLinearOrder : LinearOrder ZFReal where
  toDecidableLE _ _ := Classical.dec _
  le_refl a := Or.inr rfl
  lt_iff_le_not_ge a b := by
    have u := ZFQuotient.choose_repr a
    have v := ZFQuotient.choose_repr b
    rw [le_def, le, le_def, le, not_or, ←and_rotate, ←and_assoc, and_or_left, eq_comm,
      not_and_self_iff, or_false, and_assoc, and_rotate, ←lt_def, ←lt_def, iff_self_and]
    intro h
    constructor
    · exact ZFReal.not_gt_of_lt h
    · exact ZFReal.ne_of_lt h
  le_trans a b c ab_h bc_h := by
    rcases ab_h with ab_h | rfl <;> rcases bc_h with bc_h | rfl
    · apply Or.inl
      have u := ZFQuotient.choose_repr a
      have v := ZFQuotient.choose_repr b
      have w := ZFQuotient.choose_repr c
      rw [← class_of_mem_eq_self u, ← class_of_mem_eq_self w, ←lt_def, lt_class_of]
      rw [← class_of_mem_eq_self u, ← class_of_mem_eq_self v, ←lt_def, lt_class_of] at ab_h
      rw [← class_of_mem_eq_self v, ← class_of_mem_eq_self w, ←lt_def, lt_class_of] at bc_h
      obtain ⟨ab_s, ab_sp, ab_N, ab_hN⟩ := ab_h
      obtain ⟨bc_s, bc_sp, bc_N, bc_hN⟩ := bc_h
      have ⟨N, hN⟩ := exists_for_both ⟨ab_N, ab_hN⟩ ⟨bc_N, bc_hN⟩
      exists ab_s + bc_s, add_pos ab_sp bc_sp, N
      intro n nb
      specialize hN n nb
      obtain ⟨hab, hbc⟩ := hN
      rw [←add_lt_add_iff_right bc_s, add_assoc] at hab
      exact lt_trans hab hbc
    · exact Or.inl ab_h
    · exact Or.inl bc_h
    · exact Or.inr rfl
  le_antisymm a b := by
    rw [le_def, le, ←lt_def, le_def, le, ←lt_def]
    intro h
    rcases h with h | rfl
    · rw [or_iff_right (ZFReal.not_gt_of_lt h), eq_comm, imp_self]
      trivial
    · rw [eq_self_iff_true, or_true, imp_true_iff]
      trivial
  le_total a b := by
    rw [le_def, le, ←lt_def, le_def, le, ←lt_def, or_or_or_comm, eq_comm, or_self, or_assoc]
    have l := @ZFReal.not_gt_of_lt a b
    have r := @ZFReal.ne_of_lt a b
    by_cases hnlt : a < b
    · exact Or.inl hnlt
    apply Or.inr
    by_cases hne :  b = a
    · apply Or.inr hne
    apply Or.inl
    have u := ZFQuotient.choose_repr a
    have v := ZFQuotient.choose_repr b
    rw [← class_of_mem_eq_self u, ← class_of_mem_eq_self v] at hnlt hne ⊢
    rw [lt_class_of] at hnlt ⊢
    rw [class_eq_iff_related] at hne
    apply away_of_ne at hne
    push Not at *
    obtain ⟨e, ep, N, hN⟩ := hne
    conv at hN =>
      enter [n, nb]
      rw [lt_abs, neg_sub]
      congr <;> rw [lt_sub_iff_add_lt]
    have ⟨NC, hC⟩  := exists_for_both₂
      (isCauchy_of_carrier (of_in_class u) (e / 3) (div_pos ep three_pos))
      (isCauchy_of_carrier (of_in_class v) (e / 3) (div_pos ep three_pos))
    specialize hnlt e ep (max N NC)
    obtain ⟨n, nb, hn⟩ := hnlt
    rw [←not_lt, add_comm] at hn
    obtain hn := hN n (lt_of_le_of_lt (le_max_left N NC) nb) |>.resolve_left hn
    exists (e / 3), div_pos ep three_pos, max N NC
    intro m mb
    specialize hC n m (lt_of_le_of_lt (le_max_right N NC) nb)
      (lt_of_le_of_lt (le_max_right N NC) mb)
    obtain ⟨hu, hv⟩ := hC
    rw [abs_sub_comm] at hv
    apply lt_of_abs_lt at hu
    apply lt_of_abs_lt at hv
    rw [sub_lt_iff_lt_add'] at hu hv
    rw [← add_lt_add_iff_right (e / 3), add_assoc, ←two_mul] at hv
    apply lt_trans hv
    rw [add_comm, ←mul_one e, ←Field.mul_inv_cancel 3 three_ne_zero, ←mul_assoc, ←div_eq_mul_inv,
      mul_comm, ←two_add_one_eq_three, right_distrib, one_mul, two_add_one_eq_three, add_div,
      ←add_assoc, ← add_lt_add_iff_right (-(e / 3)), add_assoc, add_neg_cancel, add_zero,
      mul_div_assoc] at hn
    rw [←sub_lt_iff_lt_add, sub_eq_add_neg] at hu
    apply lt_trans hn hu

noncomputable instance : Preorder ZFReal := instLinearOrder.toPreorder
noncomputable instance : PartialOrder ZFReal := instLinearOrder.toPartialOrder

protected lemma mul_le_mul_of_nonneg_left {a : ZFReal} (nna : 0 ≤ a) {b c : ZFReal} (blec : b ≤ c) :
    a * b ≤ a * c := by
    rw [le_iff_eq_or_lt] at ⊢ blec nna
    rcases nna with rfl | pa
    · rw [zero_mul, zero_mul]
      exact Or.inl rfl
    rcases blec with rfl | h
    · exact Or.inl rfl
    apply Or.inr
    have u := ZFQuotient.choose_repr a
    have v := ZFQuotient.choose_repr b
    have w := ZFQuotient.choose_repr c
    rw [← class_of_mem_eq_self v, ← class_of_mem_eq_self w] at h ⊢
    rw [← class_of_mem_eq_self u] at pa ⊢
    rw [zero_def, zero, ofRat] at pa
    conv => congr <;> rw [mul_def, mul, map₂_class_of]
    rw [lt_class_of] at ⊢ h pa
    obtain ⟨a_s, a_sp, pa⟩ := pa
    obtain ⟨s, sp, h⟩ := h
    obtain ⟨N, hN⟩ := exists_for_both pa h
    clear pa h
    exists a_s * s, mul_pos a_sp sp, N
    intro n nb
    specialize hN n nb
    obtain ⟨pu, vltw⟩ := hN
    rw [apply_lambda_cauchy, Equiv.apply_symm_apply, zero_add] at pu
    conv => congr <;> rw [apply_lambda_cauchy]
    apply lt_of_mul_lt_mul_left _ (le_of_lt <| inv_pos.mpr <| lt_trans a_sp  pu)
    rw [left_distrib]
    conv => congr <;> rw [inv_mul_cancel_left₀ (Ne.symm <| ne_of_lt <| lt_trans a_sp  pu)]
    apply lt_trans' vltw
    rw [add_lt_add_iff_left, ←mul_assoc]
    apply lt_of_mul_lt_mul_left  _ (le_of_lt <| lt_trans a_sp  pu)
    rw [←mul_assoc, ←mul_assoc, Field.mul_inv_cancel _ (Ne.symm <| ne_of_lt <| lt_trans a_sp  pu),
      one_mul]
    apply lt_of_mul_lt_mul_right  _ (le_of_lt <| inv_pos.mpr <| sp)
    conv => congr <;> rw [mul_assoc, Field.mul_inv_cancel _ (Ne.symm <| ne_of_lt <| sp), mul_one]
    exact pu

instance : IsOrderedRing ZFReal where
  zero_le_one := by
    rw [zero_def, zero, one_def, one, ←ofRat_le]
    exact Or.inl one_pos
  add_le_add_left a b aleb c := by
    rw [le_iff_eq_or_lt] at ⊢ aleb
    rcases aleb with rfl | h
    · exact Or.inl rfl
    apply Or.inr
    have u := ZFQuotient.choose_repr a
    have v := ZFQuotient.choose_repr b
    have w := ZFQuotient.choose_repr c
    rw [← class_of_mem_eq_self u, ← class_of_mem_eq_self v] at h ⊢
    rw [← class_of_mem_eq_self w]
    conv => congr <;> rw [add_def, add, map₂_class_of]
    rw [lt_class_of] at ⊢ h
    conv =>
      enter [1, s, 2, 1, N, n, nb]
      conv => congr <;> rw [apply_lambda_cauchy]
      rw [←add_rotate, add_lt_add_iff_right, add_comm]
    exact h
  mul_le_mul_of_nonneg_left := @ZFReal.mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right a nna b c blec := by
    conv => congr <;> rw [mul_comm]
    exact ZFReal.mul_le_mul_of_nonneg_left nna blec

instance : IsStrictOrderedRing ZFReal where

end ZFReal

end Reals
end ZFSet

end
