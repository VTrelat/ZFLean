/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

import ZFLean.Basic
import ZFLean.Booleans
import ZFLean.Integers
public import ZFLean.Functions

/-!
# Disjoint sums and options over ZF sets

This file defines the disjoint sum `A ⊎ B` of two `ZFSet`s as a subtype, with
constructors, eliminators, and an equivalence to the type-level sum. It also develops
`Option S` together with bijections relating it to `_root_.Option` and a lifting of
functions to options.
-/

public section

namespace ZFSet

@[expose] def Sum (A B : ZFSet) :=
  {x // x ∈ (ZFSet.prod { ZFBool.false.val } A) ∪ (ZFSet.prod { ZFBool.true.val } B)}
infixr:50 " ⊎ " => Sum

namespace Sum
def inl {A B : ZFSet} (a : {x // x ∈ A}) : Sum A B :=
  ⟨ZFSet.pair ZFBool.false a,
    mem_union.mpr (Or.inl <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, a.prop⟩)⟩
def inr {A B : ZFSet} (b : {x // x ∈ B}) : Sum A B :=
  ⟨ZFSet.pair ZFBool.true b,
    mem_union.mpr (Or.inr <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, b.prop⟩)⟩

theorem inl.injEq {A B : ZFSet} {x y : {x // x ∈ A}} : (inl x : A ⊎ B) = inl y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    rw [pair_inj] at heq
    exact Subtype.val_inj.mp heq.2
  · intro
    congr

theorem inr.injEq {A B : ZFSet} {x y : {x // x ∈ B}} : (inr x : A ⊎ B) = inr y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    rw [pair_inj] at heq
    exact Subtype.val_inj.mp heq.2
  · intro
    congr

theorem cases {A B : ZFSet} (x : A ⊎ B) : x.val.π₂ ∈ A ∨ x.val.π₂ ∈ B := by
  let ⟨x, hx⟩ := x
  rw [mem_union, mem_prod] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
  · rw [mem_union, pair_mem_prod] at hx
    obtain ⟨ha, bA⟩ | hb := hx
    · rw [mem_singleton] at ha
      left
      rwa [π₂_pair]
    · rw [pair_mem_prod, mem_singleton] at hb
      right
      rw [π₂_pair]
      exact hb.2
  · rw [mem_prod] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [mem_union, pair_mem_prod] at hx
    obtain ⟨ha, aB⟩ | hb := hx
    · rw [mem_singleton] at ha
      left
      rwa [π₂_pair]
    · rw [pair_mem_prod, mem_singleton] at hb
      right
      rw [π₂_pair]
      exact hb.2

@[cases_eliminator]
noncomputable def casesOn.{u, v} {A B : ZFSet.{u}} {motive : A ⊎ B → Sort v} (x : A ⊎ B)
  (inl : (val : {x // x ∈ A}) → motive (inl val))
  (inr : (val : {x // x ∈ B}) → motive (inr val)) : motive x := by
  by_cases h : x.val.π₁ = ZFBool.false.val
  · have : x.val.π₂ ∈ A := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rwa [π₂_pair]
      · dsimp at h
        rw [pair_eta hx, pair_mem_prod, mem_singleton, h] at hx
        nomatch zftrue_ne_zffalse hx.1.symm
    have : x = Sum.inl ⟨x.val.π₂, this⟩ := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [π₁_pair] at h
        subst a
        congr 2
        dsimp
        rw [π₂_pair]
      · rw [pair_eta hx, pair_mem_prod, mem_singleton, h] at hx
        nomatch zftrue_ne_zffalse hx.1.symm
    rw [this]
    apply inl
  · have x₁_eq_true : x.val.π₁ = ZFBool.true := by
      have := Subtype.property x
      rw [mem_union, mem_prod] at this
      obtain ⟨a, ha, b, hb, eq⟩ | hx := this
      · rw [eq, π₁_pair] at h
        rw [mem_singleton] at ha
        contradiction
      · rw [pair_eta hx, pair_mem_prod, mem_singleton] at hx
        exact hx.1
    have : x.val.π₂ ∈ B := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [mem_union, pair_mem_prod, mem_singleton] at hx
        obtain ⟨rfl, -⟩ | hb := hx
        · rw [π₁_pair] at x₁_eq_true
          nomatch zftrue_ne_zffalse x₁_eq_true.symm
        · rw [pair_mem_prod] at hb
          rw [π₂_pair]
          exact hb.2
      · rw [pair_eta hx, pair_mem_prod, mem_singleton] at hx
        exact hx.2
    have : x = Sum.inr ⟨x.val.π₂, this⟩ := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [mem_union, pair_mem_prod, mem_singleton] at hx
        obtain ⟨rfl, -⟩ | hb := hx
        · rw [π₁_pair] at x₁_eq_true
          nomatch zftrue_ne_zffalse x₁_eq_true.symm
        · congr 2
          · dsimp
            rwa [π₁_pair] at x₁_eq_true
          · dsimp
            rw [π₂_pair]
      · congr
        conv_lhs => rw [pair_eta hx]
        rw [pair_inj]
        exact ⟨x₁_eq_true, rfl⟩
    rw [this]
    apply inr

@[simp]
theorem casesOn_of_inl {A B : ZFSet} {motive : A ⊎ B → Sort*} (a : {x // x ∈ A})
  (inl_case : (val : {x // x ∈ A}) → motive (inl val))
  (inr_case : (val : {x // x ∈ B}) → motive (inr val)) :
    casesOn (inl a) inl_case inr_case = inl_case a := by
  rw [casesOn, dite_cond_eq_true (eq_true (by rw [inl, π₁_pair]))]
  dsimp
  rw [cast_eq_iff_heq]
  congr
  unfold inl
  rw [π₂_pair]

@[simp]
theorem casesOn_of_inr {A B : ZFSet} {motive : A ⊎ B → Sort*} (a : {x // x ∈ B})
  (inl_case : (val : {x // x ∈ A}) → motive (inl val))
  (inr_case : (val : {x // x ∈ B}) → motive (inr val)) :
    casesOn (inr a) inl_case inr_case = inr_case a := by
  rw [casesOn, dite_cond_eq_false (eq_false ?_)]
  · dsimp
    rw [cast_eq_iff_heq]
    congr
    unfold inr
    rw [π₂_pair]
  · rw [inr, π₁_pair]
    exact zftrue_ne_zffalse

/--
Uniqueness half of the universal property of the disjoint sum: `casesOn` is the *only*
family agreeing with `inl_case` along `inl` and with `inr_case` along `inr`.
-/
theorem casesOn_unique {A B : ZFSet} {motive : A ⊎ B → Sort*}
  (inl_case : Π a, motive (inl a)) (inr_case : Π b, motive (inr b)) (g : Π x, motive x)
  (hinl : ∀ a, g (inl a) = inl_case a) (hinr : ∀ b, g (inr b) = inr_case b) (x : A ⊎ B) :
    g x = casesOn x inl_case inr_case := by
  cases x with
  | inl a => rw [hinl, casesOn_of_inl]
  | inr b => rw [hinr, casesOn_of_inr]

noncomputable def equivSum {A B : ZFSet} : A ⊎ B ≃ ({x // x ∈ A} ⊕ {x // x ∈ B}) where
  toFun x := by
    cases x with
    | inl a => exact _root_.Sum.inl a
    | inr b => exact _root_.Sum.inr b
  invFun x := by
    cases x with
    | inl a => exact inl a
    | inr b => exact inr b
  left_inv := by
    intro x
    cases x with
    | inl a =>
      beta_reduce
      conv_lhs => rw [casesOn_of_inl]
    | inr b =>
      beta_reduce
      conv_lhs => rw [casesOn_of_inr]
  right_inv := by
    intro x
    cases x with
    | inl a => simp only [casesOn_of_inl]
    | inr b => simp only [casesOn_of_inr]

/-! ### Set-level universal property of the coproduct

Everything above states the disjoint sum at the *type* level: `A ⊎ B` is a Lean subtype and
`casesOn` eliminates into a Lean family. This section states the same universal property
*inside the model*: the objects are `ZFSet`s, the arrows are elements of `funs`, and
composition is `ZFSet.composition`. -/

/-- The underlying `ZFSet` carrier of the disjoint sum: `A ⊎ B` is `{x // x ∈ toZFSet A B}`. -/
@[expose] def toZFSet (A B : ZFSet) : ZFSet :=
  (ZFSet.prod { ZFBool.false.val } A) ∪ (ZFSet.prod { ZFBool.true.val } B)

theorem sum_eq_subtype_toZFSet {A B : ZFSet} : (A ⊎ B) = {x // x ∈ toZFSet A B} := rfl

theorem pair_false_mem_toZFSet {A B a : ZFSet} (ha : a ∈ A) :
    ZFSet.pair ZFBool.false.val a ∈ toZFSet A B :=
  mem_union.mpr <| Or.inl <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, ha⟩

theorem pair_true_mem_toZFSet {A B b : ZFSet} (hb : b ∈ B) :
    ZFSet.pair ZFBool.true.val b ∈ toZFSet A B :=
  mem_union.mpr <| Or.inr <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, hb⟩

/-- An element of `toZFSet A B` tagged by `false` has its second projection in `A`. -/
theorem mem_left_of_toZFSet {A B z : ZFSet} (hz : z ∈ toZFSet A B)
    (h : z.π₁ = ZFBool.false.val) : z.π₂ ∈ A := by
  rw [toZFSet, mem_union] at hz
  rcases hz with hz | hz
  · exact (pair_mem_prod.mp (pair_eta hz ▸ hz)).2
  · rw [pair_eta hz, pair_mem_prod, mem_singleton] at hz
    rw [hz.1] at h
    nomatch zftrue_ne_zffalse h

/-- An element of `toZFSet A B` not tagged by `false` has its second projection in `B`. -/
theorem mem_right_of_toZFSet {A B z : ZFSet} (hz : z ∈ toZFSet A B)
    (h : z.π₁ ≠ ZFBool.false.val) : z.π₂ ∈ B := by
  rw [toZFSet, mem_union] at hz
  rcases hz with hz | hz
  · rw [pair_eta hz, pair_mem_prod, mem_singleton] at hz
    exact absurd hz.1 h
  · exact (pair_mem_prod.mp (pair_eta hz ▸ hz)).2

/-- The left injection `A → A ⊎ B`, as a set-level function. -/
noncomputable def inlFun (A B : ZFSet) : ZFSet :=
  λᶻ : A → toZFSet A B | a ↦ ZFSet.pair ZFBool.false.val a

/-- The right injection `B → A ⊎ B`, as a set-level function. -/
noncomputable def inrFun (A B : ZFSet) : ZFSet :=
  λᶻ : B → toZFSet A B | b ↦ ZFSet.pair ZFBool.true.val b

@[zfun]
theorem inlFun_is_func {A B : ZFSet} : IsFunc A (toZFSet A B) (inlFun A B) :=
  lambda_isFunc fun ha => pair_false_mem_toZFSet ha

@[zfun]
theorem inrFun_is_func {A B : ZFSet} : IsFunc B (toZFSet A B) (inrFun A B) :=
  lambda_isFunc fun hb => pair_true_mem_toZFSet hb

open Classical in
/--
The mediating map `[f, g] : A ⊎ B → X` of the coproduct: it applies `f` to the elements
tagged by `false` and `g` to those tagged by `true`.
-/
noncomputable def coprod {A B X : ZFSet} (f g : ZFSet)
  (hf : IsFunc A X f := by zfun) (hg : IsFunc B X g := by zfun) : ZFSet :=
  λᶻ : toZFSet A B → X
     |       z     ↦ if hz : z ∈ toZFSet A B then
                       if h : z.π₁ = ZFBool.false.val then
                         (@ᶻf ⟨z.π₂, by
                           rw [is_func_dom_eq hf]; exact mem_left_of_toZFSet hz h⟩).val
                       else
                         (@ᶻg ⟨z.π₂, by
                           rw [is_func_dom_eq hg]; exact mem_right_of_toZFSet hz h⟩).val
                     else ∅

@[zfun]
theorem coprod_is_func {A B X f g : ZFSet} (hf : IsFunc A X f) (hg : IsFunc B X g) :
    IsFunc (toZFSet A B) X (coprod f g hf hg) := by
  apply lambda_isFunc
  intro z hz
  rw [dite_cond_eq_true (eq_true hz)]
  split_ifs <;> apply SetLike.coe_mem

/--
`[f, g]` as a partial function, so that `fapply` can be applied to it without re-running the
`zpfun` search on the (large) body of `coprod`.
-/
theorem coprod_is_pfunc {A B X f g : ZFSet} (hf : IsFunc A X f) (hg : IsFunc B X g) :
    (coprod f g hf hg).IsPFunc (toZFSet A B) X := is_func_is_pfunc (coprod_is_func hf hg)

/-- `[f, g]` computes with `f` on the left summand. -/
theorem coprod_of_inl {A B X f g : ZFSet} (hf : IsFunc A X f) (hg : IsFunc B X g)
    {a : ZFSet} (ha : a ∈ A) :
    fapply (coprod f g hf hg) (coprod_is_pfunc hf hg)
        ⟨ZFSet.pair ZFBool.false.val a, by
          rw [is_func_dom_eq (coprod_is_func hf hg)]; exact pair_false_mem_toZFSet ha⟩
      = @ᶻf ⟨a, by zdom⟩ := by
  have key : (ZFSet.pair ZFBool.false.val a).pair
      (@ᶻf ⟨a, by zdom⟩ : {x // x ∈ X}).val ∈ coprod f g hf hg := by
    rw [coprod, lambda_spec]
    refine ⟨pair_false_mem_toZFSet ha, Subtype.property _, ?_⟩
    rw [dite_cond_eq_true (eq_true (pair_false_mem_toZFSet ha)),
      dite_cond_eq_true (eq_true (π₁_pair ..))]
    simp only [π₂_pair]
  rw [fapply.of_pair (coprod_is_pfunc hf hg) key]

/-- `[f, g]` computes with `g` on the right summand. -/
theorem coprod_of_inr {A B X f g : ZFSet} (hf : IsFunc A X f) (hg : IsFunc B X g)
    {b : ZFSet} (hb : b ∈ B) :
    fapply (coprod f g hf hg) (coprod_is_pfunc hf hg)
        ⟨ZFSet.pair ZFBool.true.val b, by
          rw [is_func_dom_eq (coprod_is_func hf hg)]; exact pair_true_mem_toZFSet hb⟩
      = @ᶻg ⟨b, by zdom⟩ := by
  have key : (ZFSet.pair ZFBool.true.val b).pair
      (@ᶻg ⟨b, by zdom⟩ : {x // x ∈ X}).val ∈ coprod f g hf hg := by
    rw [coprod, lambda_spec]
    refine ⟨pair_true_mem_toZFSet hb, Subtype.property _, ?_⟩
    rw [dite_cond_eq_true (eq_true (pair_true_mem_toZFSet hb)),
      dite_cond_eq_false (eq_false ?_)]
    · simp only [π₂_pair]
    · rw [π₁_pair]
      exact zftrue_ne_zffalse
  rw [fapply.of_pair (coprod_is_pfunc hf hg) key]

theorem fapply_inlFun {A B x : ZFSet} (hx : x ∈ A) :
    fapply (inlFun A B) (is_func_is_pfunc inlFun_is_func)
        ⟨x, by zdom⟩
      = ⟨ZFSet.pair ZFBool.false.val x, pair_false_mem_toZFSet hx⟩ := by
  have key : x.pair (ZFSet.pair ZFBool.false.val x) ∈ inlFun A B := by
    rw [inlFun, lambda_spec]
    exact ⟨hx, pair_false_mem_toZFSet hx, rfl⟩
  rw [fapply.of_pair (is_func_is_pfunc inlFun_is_func) key]

theorem coprod_comp_inl {A B X f g : ZFSet} (hf : IsFunc A X f) (hg : IsFunc B X g) :
    fcomp (coprod f g hf hg) (inlFun A B) (coprod_is_func hf hg) inlFun_is_func = f := by
  rw [is_func_ext_iff (IsFunc_of_composition_IsFunc (coprod_is_func hf hg) inlFun_is_func) hf]
  intro x hx
  rw [fapply_composition (coprod_is_func hf hg) inlFun_is_func hx]
  have hval : (fapply (inlFun A B) (is_func_is_pfunc inlFun_is_func)
      ⟨x, by zdom⟩).val
      = ZFSet.pair ZFBool.false.val x := congrArg Subtype.val (fapply_inlFun hx)
  simp only [hval]
  exact coprod_of_inl hf hg hx

theorem fapply_inrFun {A B x : ZFSet} (hx : x ∈ B) :
    fapply (inrFun A B) (is_func_is_pfunc inrFun_is_func)
        ⟨x, by zdom⟩
      = ⟨ZFSet.pair ZFBool.true.val x, pair_true_mem_toZFSet hx⟩ := by
  have key : x.pair (ZFSet.pair ZFBool.true.val x) ∈ inrFun A B := by
    rw [inrFun, lambda_spec]
    exact ⟨hx, pair_true_mem_toZFSet hx, rfl⟩
  rw [fapply.of_pair (is_func_is_pfunc inrFun_is_func) key]

theorem eta_of_toZFSet {A B z : ZFSet} (hz : z ∈ toZFSet A B) : z = z.π₁.pair z.π₂ := by
  rw [toZFSet, mem_union] at hz
  rcases hz with hz | hz <;> exact pair_eta hz

theorem exists_repr_of_toZFSet {A B z : ZFSet} (hz : z ∈ toZFSet A B) :
    (∃ a ∈ A, z = ZFSet.pair ZFBool.false.val a) ∨ (∃ b ∈ B, z = ZFSet.pair ZFBool.true.val b) := by
  by_cases h : z.π₁ = ZFBool.false.val
  · exact Or.inl ⟨z.π₂, mem_left_of_toZFSet hz h, by conv_lhs => rw [eta_of_toZFSet hz, h]⟩
  · refine Or.inr ⟨z.π₂, mem_right_of_toZFSet hz h, ?_⟩
    have h1 : z.π₁ = ZFBool.true.val := by
      rw [toZFSet, mem_union] at hz
      rcases hz with hz | hz
      · rw [pair_eta hz, pair_mem_prod, mem_singleton] at hz
        exact absurd hz.1 h
      · rw [pair_eta hz, pair_mem_prod, mem_singleton] at hz
        exact hz.1
    conv_lhs => rw [eta_of_toZFSet hz, h1]

theorem coprod_comp_inr {A B X f g : ZFSet} (hf : IsFunc A X f) (hg : IsFunc B X g) :
    fcomp (coprod f g hf hg) (inrFun A B) (coprod_is_func hf hg) inrFun_is_func = g := by
  rw [is_func_ext_iff (IsFunc_of_composition_IsFunc (coprod_is_func hf hg) inrFun_is_func) hg]
  intro x hx
  rw [fapply_composition (coprod_is_func hf hg) inrFun_is_func hx]
  have hval : (fapply (inrFun A B) (is_func_is_pfunc inrFun_is_func)
      ⟨x, by zdom⟩).val
      = ZFSet.pair ZFBool.true.val x := congrArg Subtype.val (fapply_inrFun hx)
  simp only [hval]
  exact coprod_of_inr hf hg hx

theorem coprod_unique {A B X f g m : ZFSet} (hf : IsFunc A X f) (hg : IsFunc B X g)
    (hm : IsFunc (toZFSet A B) X m)
    (hl : fcomp m (inlFun A B) hm inlFun_is_func = f)
    (hr : fcomp m (inrFun A B) hm inrFun_is_func = g) :
    m = coprod f g hf hg := by
  subst hl
  subst hr
  rw [is_func_ext_iff hm (coprod_is_func hf hg)]
  intro z hz
  rcases exists_repr_of_toZFSet hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
  · rw [coprod_of_inl hf hg ha, fapply_composition hm inlFun_is_func ha]
    have hval : (fapply (inlFun A B) (is_func_is_pfunc inlFun_is_func)
        ⟨a, by zdom⟩).val
        = ZFSet.pair ZFBool.false.val a := congrArg Subtype.val (fapply_inlFun ha)
    simp only [hval]
  · rw [coprod_of_inr hf hg hb, fapply_composition hm inrFun_is_func hb]
    have hval : (fapply (inrFun A B) (is_func_is_pfunc inrFun_is_func)
        ⟨b, by zdom⟩).val
        = ZFSet.pair ZFBool.true.val b := congrArg Subtype.val (fapply_inrFun hb)
    simp only [hval]

/--
**Set-level universal property of the coproduct.** For `f ∈ A.funs X` and `g ∈ B.funs X`
there is a unique `m ∈ (toZFSet A B).funs X` whose restrictions along the two injections
`inlFun`/`inrFun` are `f` and `g`. The mediating map is `coprod f g`.

This is the statement of `Sum.casesOn` / `Sum.casesOn_unique` transported inside the model:
objects are `ZFSet`s, arrows are elements of `funs`, composition is `ZFSet.composition`.
-/
theorem funs_coprod_universal {A B X f g : ZFSet}
    (hf : f ∈ A.funs X) (hg : g ∈ B.funs X) :
    ∃! m, m ∈ (toZFSet A B).funs X ∧
      composition m (inlFun A B) A (toZFSet A B) X = f ∧
      composition m (inrFun A B) B (toZFSet A B) X = g := by
  refine ⟨coprod f g (mem_funs.mp hf) (mem_funs.mp hg), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact mem_funs.mpr (coprod_is_func (mem_funs.mp hf) (mem_funs.mp hg))
  · exact coprod_comp_inl (mem_funs.mp hf) (mem_funs.mp hg)
  · exact coprod_comp_inr (mem_funs.mp hf) (mem_funs.mp hg)
  · rintro m ⟨hm, hml, hmr⟩
    exact coprod_unique (mem_funs.mp hf) (mem_funs.mp hg) (mem_funs.mp hm) hml hmr

end Sum

/-- `Option S` is the disjoint sum `{∅} ⊎ S`. Marked reducible so that the two spellings
stay interchangeable under `rw` and `simp`. -/
@[reducible, expose] def Option (S : ZFSet) := {∅} ⊎ S

instance {T : ZFSet} : Nonempty (Option T) := ⟨Sum.inl ⟨∅, mem_singleton.mpr rfl⟩⟩

namespace Option
abbrev none {S : ZFSet} : Option S := Sum.inl ⟨∅, mem_singleton.mpr rfl⟩
abbrev some {S : ZFSet} (x : {x // x ∈ S}) : Option S := Sum.inr x

theorem some_ne_none {S : ZFSet} (x : {x // x ∈ S}) : some x ≠ none := by
  unfold some Sum.inr none Sum.inl
  intro h
  injection h with h
  rw [ZFSet.pair_inj] at h
  unfold ZFBool.false ZFBool.true zftrue zffalse at h
  obtain ⟨contr, _⟩ := h
  simp_rw [ZFSet.ext_iff, notMem_empty, iff_false, mem_singleton] at contr
  nomatch contr ∅

theorem casesOn {S : ZFSet} (x : Option S) : x = none ∨ (∃ y, x = some y) := by
  obtain ⟨x, hx⟩ := x
  rw [mem_union] at hx
  rcases hx with hx | hx <;> (
    rw [mem_prod] at hx
    obtain ⟨opt, hopt, val, hval, rfl⟩ := hx
    rw [mem_singleton] at hopt
    subst hopt
    rw [mem_union, pair_mem_prod] at hx)
  · left
    unfold none Sum.inl
    congr
    rcases hx with hx | hx
    · exact mem_singleton.mp hx.right
    · rw [pair_mem_prod, mem_singleton] at hx
      absurd hx.left
      unfold ZFBool.false ZFBool.true zftrue zffalse
      intro contr
      simp_rw [ZFSet.ext_iff, notMem_empty, false_iff, mem_singleton] at contr
      nomatch contr ∅
  · right
    rcases hx with hx | hx
    · rw [mem_singleton] at hx
      absurd hx.left
      unfold ZFBool.false ZFBool.true zftrue zffalse
      intro contr
      simp_rw [ZFSet.ext_iff, notMem_empty, iff_false, mem_singleton] at contr
      nomatch contr ∅
    · rw [pair_mem_prod] at hx
      unfold some Sum.inr
      exists ⟨val, hx.right⟩

/-- The left summand of `Option S` is a singleton: every `inl` is `none`. -/
theorem inl_eq_none {S : ZFSet} (a : {x // x ∈ ({∅} : ZFSet)}) : (Sum.inl a : Option S) = none :=
  congrArg Sum.inl (Subtype.ext (mem_singleton.mp a.2))

/--
Cases elimination for `Option`, the data-level counterpart of the disjunction
`Option.casesOn`. It is `Sum.casesOn` on `{∅} ⊎ S`, using `inl_eq_none` to collapse the
left summand.
-/
noncomputable def elim.{v} {S : ZFSet} {motive : Option S → Sort v} (x : Option S)
  (none_case : motive none) (some_case : Π y, motive (some y)) : motive x := by
  refine Sum.casesOn (motive := motive) x (fun a => ?_) some_case
  rw [inl_eq_none a]
  exact none_case

/-- Computation rule of `elim` on `none`. -/
@[simp]
theorem elim_of_none {S : ZFSet} {motive : Option S → Sort*}
  (none_case : motive none) (some_case : Π y, motive (some y)) :
    elim none none_case some_case = none_case := by
  rw [elim, Sum.casesOn_of_inl]
  rfl

/-- Computation rule of `elim` on `some`. -/
@[simp]
theorem elim_of_some {S : ZFSet} {motive : Option S → Sort*}
  (none_case : motive none) (some_case : Π y, motive (some y)) (y : {x // x ∈ S}) :
    elim (some y) none_case some_case = some_case y := by
  rw [elim, Sum.casesOn_of_inr]

/--
Uniqueness half of the universal property of `Option`: `elim` is the *only* family
agreeing with `none_case` on `none` and with `some_case` along `some`.
-/
theorem elim_unique {S : ZFSet} {motive : Option S → Sort*}
  (none_case : motive none) (some_case : Π y, motive (some y)) (g : Π x, motive x)
  (hnone : g none = none_case) (hsome : ∀ y, g (some y) = some_case y) (x : Option S) :
    g x = elim x none_case some_case := by
  refine Sum.casesOn (motive := fun x => g x = elim x none_case some_case) x (fun a => ?_) ?_
  · rw [inl_eq_none a, hnone, elim_of_none]
  · intro y
    rw [hsome, elim_of_some]

-- theorem ZFInt.into.injective : Function.Injective into := into_inj
-- theorem ZFInt.outof.injective : Function.Injective outof := outof_inj

open Classical in
noncomputable abbrev the {S : ZFSet} (S_nemp : S ≠ ∅) (x : Option S) : {x // x ∈ S} :=
  if isNone : x = none then
    ⟨ε S, epsilon_spec (nonempty_exists_iff.mp S_nemp)⟩
  else choose (Or.resolve_left (casesOn x) isNone)


section ZFOption_to_Option

open Classical in
private noncomputable def into {T : ZFSet} : Option T → _root_.Option {x // x ∈ T} := fun x ↦
  if hx : x = none then .none else .some <| Classical.choose <| Or.resolve_left (casesOn x) hx

theorem some.injEq {T : ZFSet} {x y : {x // x ∈ T}} : some x = some y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    rw [pair_inj] at heq
    exact Subtype.val_inj.mp heq.2
  · intro
    congr

theorem ne_none_is_some {T : ZFSet} (x : Option T) : x ≠ none → ∃ y, x = some y := by
  intro h
  obtain ⟨y, hy⟩ := casesOn x
  · contradiction
  · assumption

private theorem into.inj {T : ZFSet} :
    Function.Injective (into : Option T → _root_.Option {x // x ∈ T}) := by
  intro x y heq
  unfold into at heq
  split_ifs at heq with hx hy hy
  · rw [hx, hy]
  · injection heq with heq
    obtain ⟨x, rfl⟩ := ne_none_is_some x hx
    obtain ⟨y, rfl⟩ := ne_none_is_some y hy
    generalize_proofs px py at heq
    rw [Classical.choose_spec px, Classical.choose_spec py]
    congr

private theorem into.surj {T : ZFSet} :
    Function.Surjective (into : Option T → _root_.Option {x // x ∈ T}) := by
  intro y
  unfold into
  cases y with
  | none =>
    exists none
    split_ifs <;> trivial
  | some v =>
    exists (some v)
    split_ifs with h
    · nomatch some_ne_none v h
    · generalize_proofs pv
      rw [← some.injEq.mp <| Classical.choose_spec pv]

private theorem into.bij {T : ZFSet} :
  Function.Bijective (into : Option T → _root_.Option {x // x ∈ T}) := ⟨into.inj, into.surj⟩

noncomputable def EmbeddingZFOptionOption {T : ZFSet} : Option T ↪ _root_.Option {x // x ∈ T} where
  toFun := into
  inj' := into.inj

noncomputable def instEquivZFOptionOption {T : ZFSet} :
    Option T ≃ _root_.Option {x // x ∈ T} where
  toFun := into
  invFun := Function.invFun into
  left_inv := Function.leftInverse_invFun into.inj
  right_inv := Function.rightInverse_invFun into.surj

end ZFOption_to_Option

section Option_to_ZFOption

private def outof {T : ZFSet} : _root_.Option {x // x ∈ T} → Option T
  | .some ⟨x, hx⟩ => some ⟨x, hx⟩
  | .none => none

private theorem outof.inj {T : ZFSet} :
    Function.Injective (outof : _root_.Option {x // x ∈ T} → Option T) := by
  intro x y heq
  cases x <;> cases y <;> unfold outof at heq
  · rfl
  · injection heq with heq
    rw [pair_inj] at heq
    absurd heq.1
    unfold ZFBool.false ZFBool.true zftrue zffalse
    intro contr
    rw [Subtype.val_inj] at contr
    injection contr with contr
    rw [ZFSet.ext_iff] at contr
    exact (notMem_empty ∅) <| (mem_singleton.eq ▸ contr ∅).mpr rfl
  · injection heq with heq
    rw [pair_inj] at heq
    absurd heq.1
    unfold ZFBool.false ZFBool.true zftrue zffalse
    intro contr
    rw [Subtype.val_inj] at contr
    injection contr with contr
    rw [ZFSet.ext_iff] at contr
    exact (notMem_empty ∅) <| (mem_singleton.eq ▸ contr ∅).mp rfl
  · injection heq with heq
    rw [pair_inj] at heq
    have := Subtype.val_inj.mp <| Subtype.mk_eq_mk.mp <| Subtype.val_inj.mp heq.2
    congr

private theorem outof.surj {T : ZFSet} :
    Function.Surjective (outof : _root_.Option {x // x ∈ T} → Option T) := by
  intro y
  unfold outof
  rcases y.casesOn with rfl | ⟨x, rfl⟩
  · exists .none
  · exists .some x

private theorem outof.bij {T : ZFSet} :
  Function.Bijective (outof : _root_.Option {x // x ∈ T} → Option T) := ⟨outof.inj, outof.surj⟩

def EmbeddingOptionZFOption {T : ZFSet} : _root_.Option {x // x ∈ T} ↪ Option T where
  toFun := outof
  inj' := outof.inj

noncomputable def instEquivOptionZFOption {T : ZFSet} :
    _root_.Option {x // x ∈ T} ≃ Option T where
  toFun := outof
  invFun := Function.invFun outof
  left_inv := Function.leftInverse_invFun outof.inj
  right_inv := Function.rightInverse_invFun outof.surj

end Option_to_ZFOption

abbrev toZFSet (T : ZFSet) :
  ZFSet := (ZFSet.prod { ZFBool.false.val } {∅}) ∪ (ZFSet.prod { ZFBool.true.val } T)

open Classical in
noncomputable def flift {A B : ZFSet} (f : ZFSet)
  (hf : IsFunc A B f := by zfun) :
    {f' : ZFSet // IsFunc (Option.toZFSet A) (Option.toZFSet B) f'} :=
  let f' : ZFSet :=
    λᶻ: Option.toZFSet A → Option.toZFSet B
      |          x       ↦ if hx : x ∈ Option.toZFSet A then
                              if isSome : ∃ y, ⟨x, hx⟩ = some y then
                                let ⟨y, hy⟩ := Classical.choose isSome
                                some (S := B) (@ᶻf ⟨y, by zdom⟩) |>.val
                              else none (S := B).val
                            else ∅
  have hf' : IsFunc (Option.toZFSet A) (Option.toZFSet B) f' := by
    apply ZFSet.lambda_isFunc
    intro x hx
    rw [dite_cond_eq_true (eq_true hx)]
    split_ifs with isSome <;> apply SetLike.coe_mem
  ⟨f', hf'⟩

theorem flift_bijective {f A B : ZFSet} (hf : IsFunc A B f) :
    (ZFSet.Option.flift f).val.IsBijective (Subtype.property _) ↔ f.IsBijective hf where
  mp := by
    rintro ⟨hinj, hsurj⟩
    and_intros
    · intro x y z hx hy hz xz yz
      specialize hinj (Option.some ⟨x, hx⟩).val (Option.some ⟨y, hy⟩).val (Option.some ⟨z, hz⟩).val
        (SetLike.coe_mem _) (SetLike.coe_mem _) (SetLike.coe_mem _) ?_ ?_
      · rw [flift, lambda_spec]
        refine ⟨SetLike.coe_mem _, SetLike.coe_mem _, ?_⟩
        split_ifs with h1 h2
        · have hc : Classical.choose h2 = ⟨x, hx⟩ :=
            Option.some.injEq.mp (Classical.choose_spec h2).symm
          simp only [hc]
          exact Subtype.ext_iff.mp <|
            congrArg (Option.some (S := B)) (fapply.of_pair _ xz).symm
        · exact absurd ⟨⟨x, hx⟩, rfl⟩ h2
        · exact absurd (SetLike.coe_mem _) h1
      · rw [flift, lambda_spec]
        refine ⟨SetLike.coe_mem _, SetLike.coe_mem _, ?_⟩
        split_ifs with h1 h2
        · have hc : Classical.choose h2 = ⟨y, hy⟩ :=
            Option.some.injEq.mp (Classical.choose_spec h2).symm
          simp only [hc]
          exact Subtype.ext_iff.mp <|
            congrArg (Option.some (S := B)) (fapply.of_pair _ yz).symm
        · exact absurd ⟨⟨y, hy⟩, rfl⟩ h2
        · exact absurd (SetLike.coe_mem _) h1
      · exact Subtype.ext_iff.mp <| Option.some.injEq.mp <| Subtype.ext_iff.mpr hinj
    · intro y hy
      have : (Option.some ⟨y, hy⟩).val ∈ Option.toZFSet B :=
        SetLike.coe_mem _
      obtain ⟨x, hx, xy⟩ := hsurj _ this
      rw [flift, lambda_spec, dite_cond_eq_true (eq_true hx)] at xy
      obtain ⟨-, -, eq⟩ := xy
      split_ifs at eq with issome
      · obtain rfl := Subtype.ext_iff.mp <| Option.some.injEq.mp <| Subtype.ext_iff.mpr eq
        use (Classical.choose issome).val
        and_intros
        · apply SetLike.coe_mem
        · apply fapply.def
      · nomatch ZFSet.Option.some_ne_none _ (Subtype.val_inj.mp eq)
  mpr := by
    intro hbij
    rw [bijective_exists1_iff] at hbij ⊢
    intro y hy
    obtain eq | ⟨⟨y, hy⟩, eq⟩ := Option.casesOn ⟨y, hy⟩ <;>
      obtain rfl := Subtype.ext_iff.mp eq
    · use (@none A).val
      and_intros
      · apply SetLike.coe_mem
      · rw [flift, lambda_spec]
        refine ⟨SetLike.coe_mem _, SetLike.coe_mem _, ?_⟩
        split_ifs with h1 isnone
        · obtain ⟨_, contr⟩ := isnone
          change none = some _ at contr
          nomatch ZFSet.Option.some_ne_none _ contr.symm
        · rfl
        · exact absurd (SetLike.coe_mem _) h1
      · rintro y ⟨hy, pair⟩
        rw [flift, lambda_spec] at pair
        obtain ⟨-, -, eq⟩ := pair
        rw [dite_cond_eq_true (eq_true hy)] at eq
        split_ifs at eq with issome
        · nomatch ZFSet.Option.some_ne_none _ (Subtype.val_inj.mp eq).symm
        · have := @ZFSet.Option.ne_none_is_some _ ⟨y, hy⟩
          rw [imp_iff_not issome, not_not] at this
          exact Subtype.ext_iff.mp this
    · obtain ⟨x, ⟨hx, fxy⟩, x_unq⟩ := hbij y ‹_›
      use (Option.some ⟨x, hx⟩).val
      and_intros
      · apply SetLike.coe_mem
      · rw [flift, lambda_spec]
        refine ⟨SetLike.coe_mem _, SetLike.coe_mem _, ?_⟩
        split_ifs with h1 isnone
        · have := Classical.choose_spec isnone
          change some _ = some _ at this
          rw [Option.some.injEq, Subtype.ext_iff] at this
          dsimp at this
          refine Subtype.ext_iff.mp (congrArg (Option.some (S := B)) ?_)
          symm
          apply fapply.of_pair
          rwa [this] at fxy
        · exact absurd ⟨⟨x, hx⟩, rfl⟩ isnone
        · exact absurd (SetLike.coe_mem _) h1
      · rintro z ⟨hz, fzy⟩
        rw [flift, lambda_spec] at fzy
        obtain ⟨-, -, eq⟩ := fzy
        rw [dite_cond_eq_true (eq_true hz)] at eq
        split_ifs at eq with issome
        · obtain rfl := Subtype.ext_iff.mp <| Option.some.injEq.mp <| Subtype.ext_iff.mpr eq
          have := Subtype.ext_iff.mp <| Classical.choose_spec issome
          dsimp at this
          rw [this]
          refine Subtype.ext_iff.mp (congrArg (Option.some (S := A)) ?_)
          have := fapply.of_pair (is_func_is_pfunc hf) fxy
          simp only [Subtype.coe_eta] at this
          rw [←bijective_exists1_iff hf] at hbij
          symm
          have := IsInjective.apply_inj hf hbij.1 this
          rwa [Subtype.ext_iff] at this ⊢
        · nomatch ZFSet.Option.some_ne_none _ (Subtype.val_inj.mp eq)

end Option

end ZFSet

end
