/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import ZFLean.Functions

/-!
# Set-level recursion on the natural numbers

`ZFNat.rec` and `ZFNat.rec_unique` state the universal property of the naturals at the *type*
level: the motive is a Lean family and the recursor is a Lean definition. This file states the
same property *inside the model*: `Nat` is a `ZFSet`, arrows are elements of `funs`, the
successor is the set-level function `succFun`, and composition is `ZFSet.composition`.

The main result is `funs_nat_recursion`: for `x ∈ X` and a step function `s ∈ X.funs X` there
is a unique `h ∈ Nat.funs X` with `h ∅ = x` and `h ∘ᶻ succFun = s ∘ᶻ h`. In categorical terms,
`(Nat, ∅, succFun)` is a natural numbers object in the category of `ZFSet`s and `funs`.
-/

public noncomputable section

namespace ZFSet

/-! ## The successor as a set-level function -/

/-- The successor function `Nat → Nat`, as an element of `Nat.funs Nat`. -/
noncomputable def succFun : ZFSet := λᶻ : Nat → Nat | n ↦ insert n n

@[zfun]
theorem succFun_is_func : IsFunc Nat Nat succFun :=
  lambda_isFunc fun hn => ZFNat.succ_mem_Nat' hn

theorem succFun_is_pfunc : succFun.IsPFunc Nat Nat := is_func_is_pfunc succFun_is_func

theorem succFun_mem_funs : succFun ∈ funs Nat Nat := mem_funs.mpr succFun_is_func

theorem fapply_succFun {n : ZFSet} (hn : n ∈ Nat) :
    fapply succFun succFun_is_pfunc ⟨n, by zdom⟩
      = ⟨insert n n, ZFNat.succ_mem_Nat' hn⟩ := by
  have key : n.pair (insert n n) ∈ succFun := by
    rw [succFun, lambda_spec]
    exact ⟨hn, ZFNat.succ_mem_Nat' hn, rfl⟩
  rw [fapply.of_pair succFun_is_pfunc key]

/-! ## The iterate of a step function -/

/--
The `n`-th iterate of `s` applied to `x`, at the type level. This is `ZFNat.rec` with the
constant motive `{y // y ∈ X}`; `recFun` is its transport into the model.
-/
noncomputable def recVal {X : ZFSet} (x s : ZFSet) (hx : x ∈ X) (hs : IsFunc X X s) :
    ZFNat → {y // y ∈ X} :=
  fun n => ZFNat.rec (motive := fun _ => {y // y ∈ X}) n ⟨x, hx⟩
    fun _ ih => @ᶻs ⟨ih.val, by zdom⟩

theorem recVal_zero {X : ZFSet} {x s : ZFSet} (hx : x ∈ X) (hs : IsFunc X X s) :
    recVal x s hx hs 0 = ⟨x, hx⟩ := ZFNat.rec_zero ..

theorem recVal_succ {X : ZFSet} {x s : ZFSet} (hx : x ∈ X) (hs : IsFunc X X s) (n : ZFNat) :
    recVal x s hx hs n.succ
      = @ᶻs ⟨(recVal x s hx hs n).val, by zdom⟩ :=
  ZFNat.rec_succ ..

/-! ## The recursor as a set -/

open Classical in
/-- The set-level recursor: the element of `Nat.funs X` sending `n` to `sⁿ x`. -/
noncomputable def recFun {X : ZFSet} (x s : ZFSet) (hx : x ∈ X) (hs : IsFunc X X s) : ZFSet :=
  λᶻ : Nat → X | n ↦ if hn : n ∈ Nat then (recVal x s hx hs ⟨n, hn⟩).val else ∅

@[zfun]
theorem recFun_is_func {X : ZFSet} {x s : ZFSet} (hx : x ∈ X) (hs : IsFunc X X s) :
    IsFunc Nat X (recFun x s hx hs) := by
  apply lambda_isFunc
  intro n hn
  rw [dite_cond_eq_true (eq_true hn)]
  exact Subtype.property _

/--
`recFun` as a partial function, so that `fapply` can be applied to it without re-running the
`zpfun` search on the (large) body of `recFun`.
-/
theorem recFun_is_pfunc {X : ZFSet} {x s : ZFSet} (hx : x ∈ X) (hs : IsFunc X X s) :
    (recFun x s hx hs).IsPFunc Nat X := is_func_is_pfunc (recFun_is_func hx hs)

theorem recFun_mem_funs {X : ZFSet} {x s : ZFSet} (hx : x ∈ X) (hs : IsFunc X X s) :
    recFun x s hx hs ∈ funs Nat X := mem_funs.mpr (recFun_is_func hx hs)

/-- `recFun` applied inside the model agrees with the type-level iterate `recVal`. -/
theorem fapply_recFun {X : ZFSet} {x s : ZFSet} (hx : x ∈ X) (hs : IsFunc X X s)
    {n : ZFSet} (hn : n ∈ Nat) :
    fapply (recFun x s hx hs) (recFun_is_pfunc hx hs)
        ⟨n, by rw [is_func_dom_eq (recFun_is_func hx hs)]; exact hn⟩
      = recVal x s hx hs ⟨n, hn⟩ := by
  have key : n.pair (recVal x s hx hs ⟨n, hn⟩).val ∈ recFun x s hx hs := by
    rw [recFun, lambda_spec]
    exact ⟨hn, Subtype.property _, by rw [dite_cond_eq_true (eq_true hn)]⟩
  rw [fapply.of_pair (recFun_is_pfunc hx hs) key]

/-! ## The universal property -/

/-- `recFun` sends `∅` — the set-level zero — to `x`. -/
theorem recFun_zero {X : ZFSet} {x s : ZFSet} (hx : x ∈ X) (hs : IsFunc X X s) :
    ZFSet.pair ∅ x ∈ recFun x s hx hs := by
  rw [recFun, lambda_spec]
  refine ⟨ZFNat.zero_in_Nat, hx, ?_⟩
  rw [dite_cond_eq_true (eq_true ZFNat.zero_in_Nat)]
  exact congrArg Subtype.val (recVal_zero hx hs).symm

/-- `recFun` satisfies the recursion equation `h ∘ᶻ succFun = s ∘ᶻ h`. -/
theorem recFun_comp_succFun {X : ZFSet} {x s : ZFSet} (hx : x ∈ X) (hs : IsFunc X X s) :
    composition (recFun x s hx hs) succFun Nat Nat X
      = composition s (recFun x s hx hs) Nat X X := by
  rw [is_func_ext_iff
    (IsFunc_of_composition_IsFunc (recFun_is_func hx hs) succFun_is_func)
    (IsFunc_of_composition_IsFunc hs (recFun_is_func hx hs))]
  intro n hn
  rw [fapply_composition (recFun_is_func hx hs) succFun_is_func hn,
    fapply_composition hs (recFun_is_func hx hs) hn]
  have hsucc : (fapply succFun succFun_is_pfunc
      ⟨n, by zdom⟩).val = insert n n :=
    congrArg Subtype.val (fapply_succFun hn)
  have hrec : (fapply (recFun x s hx hs) (recFun_is_pfunc hx hs)
      ⟨n, by rw [is_func_dom_eq (recFun_is_func hx hs)]; exact hn⟩).val
      = (recVal x s hx hs ⟨n, hn⟩).val :=
    congrArg Subtype.val (fapply_recFun hx hs hn)
  simp only [hsucc, hrec]
  rw [fapply_recFun hx hs (ZFNat.succ_mem_Nat' hn)]
  exact recVal_succ hx hs ⟨n, hn⟩

/--
Uniqueness: any `h : Nat → X` with `h ∅ = x` and `h ∘ᶻ succFun = s ∘ᶻ h` is `recFun x s`.

The proof is `ZFNat.rec_unique` — the *typed* uniqueness lemma — applied to the family
`fun k ↦ h k`, so the set-level statement is discharged by the type-level one.
-/
theorem recFun_unique {X : ZFSet} {x s h : ZFSet} (hx : x ∈ X) (hs : IsFunc X X s)
    (hh : IsFunc Nat X h) (h0 : ZFSet.pair ∅ x ∈ h)
    (hstep : composition h succFun Nat Nat X = composition s h Nat X X) :
    h = recFun x s hx hs := by
  -- `h` applied inside the model, read as a type-level family over `ZFNat`.
  have H_zero : fapply h (is_func_is_pfunc hh)
      ⟨(0 : ZFNat).val, by zdom⟩ = ⟨x, hx⟩ :=
    fapply.of_pair (is_func_is_pfunc hh) h0
  have H_succ : ∀ k : ZFNat,
      fapply h (is_func_is_pfunc hh)
          ⟨k.succ.val, by zdom⟩
        = @ᶻs ⟨(fapply h (is_func_is_pfunc hh)
              ⟨k.val, by zdom⟩).val,
            by zdom⟩ := by
    intro k
    have hn := k.property
    have hpt := (is_func_ext_iff (IsFunc_of_composition_IsFunc hh succFun_is_func)
      (IsFunc_of_composition_IsFunc hs hh)).mp hstep k.val hn
    rw [fapply_composition hh succFun_is_func hn, fapply_composition hs hh hn] at hpt
    have hsucc : (fapply succFun succFun_is_pfunc
        ⟨k.val, by zdom⟩).val = insert k.val k.val :=
      congrArg Subtype.val (fapply_succFun hn)
    simp only [hsucc] at hpt
    exact hpt
  -- the typed uniqueness lemma discharges the set-level one
  have key : ∀ k : ZFNat,
      fapply h (is_func_is_pfunc hh) ⟨k.val, by zdom⟩
        = recVal x s hx hs k :=
    ZFNat.rec_unique (motive := fun _ => {y // y ∈ X}) ⟨x, hx⟩
      (fun _ ih => @ᶻs ⟨ih.val, by zdom⟩)
      (fun k => fapply h (is_func_is_pfunc hh)
        ⟨k.val, by zdom⟩)
      H_zero H_succ
  rw [is_func_ext_iff hh (recFun_is_func hx hs)]
  intro n hn
  rw [fapply_recFun hx hs hn]
  exact key ⟨n, hn⟩

/--
**Set-level recursion theorem for the naturals.** For `x ∈ X` and a step function
`s ∈ X.funs X` there is a unique `h ∈ Nat.funs X` with `h ∅ = x` and
`h ∘ᶻ succFun = s ∘ᶻ h`; the witness is `recFun x s`.

Equivalently: `(Nat, ∅, succFun)` is a natural numbers object for `ZFSet`s and `funs`.
-/
theorem funs_nat_recursion {X x s : ZFSet} (hx : x ∈ X) (hs : s ∈ funs X X) :
    ∃! h, h ∈ funs Nat X ∧
      ZFSet.pair ∅ x ∈ h ∧
      composition h succFun Nat Nat X = composition s h Nat X X := by
  refine ⟨recFun x s hx (mem_funs.mp hs), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact recFun_mem_funs hx (mem_funs.mp hs)
  · exact recFun_zero hx (mem_funs.mp hs)
  · exact recFun_comp_succFun hx (mem_funs.mp hs)
  · rintro h ⟨hh, h0, hstep⟩
    exact recFun_unique hx (mem_funs.mp hs) (mem_funs.mp hh) h0 hstep

end ZFSet

end
