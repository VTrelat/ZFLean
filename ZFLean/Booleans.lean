/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import ZFLean.Def
public import ZFLean.Transfer

/-!
# Boolean algebra on `ZFSet`

This file defines the boolean algebra on `ZFSet` and the type of booleans `ZFBool`.
It defines the following operations:
- `not` : negation
- `and` : conjunction
- `or` : disjunction
- `true` : ZF true value
- `false` : ZF false value
- `𝔹` : set of ZF booleans
- `toBool` : conversion from `ZFBool` to `Bool`
- `ofBool` : conversion from `Bool` to `ZFBool`
- `equivBool` : the equivalence `ZFBool ≃ Bool`, along which goals are transferred
- `equivProp` : the classical equivalence `ZFBool ≃ Prop`, the other reading of `ZFBool`

-/

public noncomputable section

namespace ZFSet
section Booleans

/-! ## ZF Boolean Algebra -/

/-- False value defined as the empty set. -/
abbrev zffalse : ZFSet := ∅
/-- True value defined as the singleton containing the empty set. -/
abbrev zftrue : ZFSet := {zffalse}
/-- Set of ZF booleans, defined as the set containing `zffalse` and `zftrue`. -/
abbrev 𝔹 : ZFSet := {zffalse,zftrue}
/-- Type of ZF booleans. -/
abbrev ZFBool := { x // x ∈ 𝔹 }

theorem zftrue_ne_zffalse : zftrue ≠ zffalse := by
  intro h
  rw [ZFSet.ext_iff, zffalse, zftrue] at h
  specialize h ∅
  rw [mem_singleton] at h
  nomatch h.mp rfl

namespace ZFBool

theorem zftrue_mem_𝔹 : zftrue ∈ 𝔹 := by
  rw [mem_insert_iff, mem_singleton]
  exact Or.inr rfl

theorem zffalse_mem_𝔹 : zffalse ∈ 𝔹 := by
  rw [mem_insert_iff, mem_singleton]
  exact Or.inl rfl

lemma 𝔹.nonempty : ZFSet.𝔹 ≠ ∅ := by
  intro h
  rw [ZFSet.ext_iff] at h
  simp only [ZFSet.notMem_empty, iff_false] at h
  nomatch h ZFSet.zffalse (ZFSet.ZFBool.zffalse_mem_𝔹)

/-- False value, lifted on `ZFBool`. -/
abbrev false : ZFBool := ⟨zffalse, zffalse_mem_𝔹⟩
/-- True value, lifted on `ZFBool`. -/
abbrev true : ZFBool := ⟨zftrue, zftrue_mem_𝔹⟩
instance Bool_top : Top ZFBool := ⟨true⟩
instance Bool_bot : Bot ZFBool := ⟨false⟩
@[simp] theorem top_eq_true : ⊤ = true := rfl
@[simp] theorem bot_eq_false : ⊥ = false := rfl
theorem true_ne_false : (⊤ : ZFBool) ≠ ⊥ := by
  intro h
  rw [top_eq_true, bot_eq_false] at h
  injection h with h
  nomatch zftrue_ne_zffalse h

@[simp]
theorem mem_𝔹_iff (p : ZFSet) : p ∈ 𝔹 ↔ p = zffalse ∨ p = zftrue := by
  rw [mem_insert_iff, mem_singleton]

@[simp]
theorem powerset_false : zffalse.powerset = zftrue := by
  unfold zftrue zffalse
  ext x
  simp only [mem_powerset, mem_singleton]
  apply Iff.intro
  · exact subset_of_empty
  · exact (subset_of_subset_of_eq (fun _ a => a) ·)

/--
The enumeration of the powerset of `𝔹`.
-/
theorem powerset_𝔹_def :
  ZFSet.𝔹.powerset = {∅, {ZFSet.zffalse}, {ZFSet.zftrue}, {ZFSet.zffalse, ZFSet.zftrue}} := by
  ext1 x
  constructor
  · intro h
    rw [ZFSet.mem_powerset, ZFSet.𝔹] at h
    simp_rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    by_cases hx : x = ∅
    · left; exact hx
    · right
      by_cases hx' : ZFSet.zffalse ∈ x
      · rw [← or_assoc, or_comm, ← or_assoc]
        left
        by_cases hx'' : ZFSet.zftrue ∈ x
        · left
          ext1 s
          constructor
          · intro hs; exact h hs
          · intro hs; rcases (ZFSet.ZFBool.mem_𝔹_iff s).mp hs with rfl | rfl <;> assumption
        · right
          ext1 s
          constructor
          · intro hs
            rw [ZFSet.mem_singleton]
            rcases ZFSet.ZFBool.mem_𝔹_iff s |>.mp (h hs) with rfl | rfl <;> trivial
          · intro hs
            rcases ZFSet.mem_singleton.mp hs
            exact hx'
      · by_cases hx'' : ZFSet.zftrue ∈ x
        · right
          left
          ext1 s
          constructor
          · intro hs
            rw [ZFSet.mem_singleton]
            rcases (ZFSet.ZFBool.mem_𝔹_iff s).mp (h hs) with rfl | rfl <;> trivial
          · intro hs
            rcases ZFSet.mem_singleton.mp hs
            exact hx''
        · simp_rw [ZFSet.subset_def, ZFSet.ZFBool.mem_𝔹_iff] at h
          obtain ⟨w, hw⟩ := nonempty_exists_iff.mp hx
          rcases h hw with rfl | rfl <;> contradiction
  · intro hx
    simp_rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rw [ZFSet.mem_powerset]
    · exact ZFSet.empty_subset ZFSet.𝔹
    · intro _ hx
      rw [ZFSet.ZFBool.mem_𝔹_iff]
      rcases ZFSet.mem_singleton.mp hx
      left; rfl
    · intro _ hx
      rw [ZFSet.ZFBool.mem_𝔹_iff]
      rcases ZFSet.mem_singleton.mp hx
      right; rfl

/-- Boolean negation, defined as the symmetric difference with `true`. -/
protected abbrev not (p : ZFBool) : ZFBool := ⟨true Δ p.1, by
  let ⟨p, hp⟩ := p
  rw [mem_𝔹_iff] at hp ⊢
  rcases hp with rfl | rfl
  · right
    exact symmDiff_empty _
  · left
    exact symmDiff_self _⟩

/-- Cases elimination for `ZFBool`. -/
@[cases_eliminator]
def casesOn {motive : ZFBool → Sort _}
  (p : ZFBool)
  (false : motive ⊥)
  (true : motive ⊤) : motive p := by
  obtain ⟨P, hP⟩ := p
  have := mem_𝔹_iff P |>.mp hP
  by_cases h : P = zffalse
  · subst h
    exact false
  · have := Or.resolve_left this h
    subst this
    exact true

/-- Computation rule of `casesOn` on `⊥`. -/
@[simp]
theorem casesOn_of_false {motive : ZFBool → Sort*}
  (false_case : motive ⊥) (true_case : motive ⊤) :
    ZFBool.casesOn ⊥ false_case true_case = false_case := by
  rw [casesOn]
  dsimp only
  split
  · rfl
  · exact absurd rfl ‹_›

/-- Computation rule of `casesOn` on `⊤`. -/
@[simp]
theorem casesOn_of_true {motive : ZFBool → Sort*}
  (false_case : motive ⊥) (true_case : motive ⊤) :
    ZFBool.casesOn ⊤ false_case true_case = true_case := by
  rw [casesOn]
  dsimp only
  split
  · exact absurd ‹_› zftrue_ne_zffalse
  · rfl

/--
Uniqueness half of the universal property of `ZFBool`: `casesOn` is the *only* family
agreeing with `false_case` on `⊥` and with `true_case` on `⊤`.
-/
theorem casesOn_unique {motive : ZFBool → Sort*}
  (false_case : motive ⊥) (true_case : motive ⊤) (g : Π p, motive p)
  (hfalse : g ⊥ = false_case) (htrue : g ⊤ = true_case) (p : ZFBool) :
    g p = ZFBool.casesOn p false_case true_case := by
  cases p using ZFBool.casesOn with
  | false => rw [hfalse, casesOn_of_false]
  | true => rw [htrue, casesOn_of_true]

/-- Boolean conjunction, defined as set intersection. -/
protected abbrev and (p q : ZFBool) : ZFBool :=
  let ⟨P, hP⟩ := p
  let ⟨Q, hQ⟩ := q
  ⟨P ∩ Q, by
    rw [mem_𝔹_iff]
    rw [mem_𝔹_iff] at hP hQ
    cases hP <;> cases hQ <;> subst_eqs
    · apply Or.inl
      ext1
      rw [mem_inter, and_self]
    · apply Or.inl
      ext1
      simp only [mem_inter, notMem_empty, false_and]
    · apply Or.inl
      ext1
      simp only [mem_inter,  notMem_empty, and_false]
    · apply Or.inr
      ext1
      simp only [mem_inter, and_self]⟩

infixl:55 " ⋀ " => ZFBool.and

protected abbrev or (p q : ZFBool) : ZFBool :=
  let ⟨P, hP⟩ := p
  let ⟨Q, hQ⟩ := q
  ⟨P ∪ Q,
    by
    rw [mem_𝔹_iff]
    rw [mem_𝔹_iff] at hP hQ
    cases hP <;> cases hQ <;> subst_eqs
    · apply Or.inl
      ext1
      rw [mem_union, or_self]
    · apply Or.inr
      ext1
      simp only [mem_union, notMem_empty, mem_singleton, false_or]
    · apply Or.inr
      ext1
      simp only [mem_union, notMem_empty, or_false]
    · apply Or.inr
      ext1
      simp only [mem_union, or_self]⟩

infixl:55 " ⋁ " => ZFBool.or

/-! ### Boolean algebra -/

@[simp]
theorem not_true_eq_false : ZFBool.not ⊤ = ⊥ := by
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_symmDiff]
  constructor
  · rintro (⟨l, r⟩ | ⟨l, r⟩) <;> nomatch r l
  · intro h
    nomatch notMem_empty _ h

@[simp]
theorem not_false_eq_true : ZFBool.not ⊥ = ⊤ := by
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_symmDiff]
  constructor
  · rintro (⟨l, r⟩ | ⟨l, r⟩)
    · exact l
    · nomatch notMem_empty _ l
  · intro h
    left
    exact ⟨h, notMem_empty _⟩

theorem and_comm (p q : ZFBool) : p ⋀ q = q ⋀ p := by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_inter]
  exact And.comm

theorem and_assoc (p q r : ZFBool) : p ⋀ q ⋀ r = p ⋀ (q ⋀ r) := by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  obtain ⟨R, hR⟩ := r
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_inter]
  exact _root_.and_assoc

@[simp]
theorem and_true (p : ZFBool) : p ⋀ ⊤ = p := by
  obtain ⟨P, hP⟩ := p
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_inter]
  rw [mem_𝔹_iff] at hP
  rw [and_iff_left_iff_imp]
  intro h
  cases hP
  · subst_eqs
    simp only [notMem_empty] at h
  · subst_eqs
    assumption

@[simp]
theorem and_false (p : ZFBool) : p ⋀ ⊥ = ⊥ := by
  obtain ⟨P, hP⟩ := p
  ext
  rw [mem_inter]
  rw [mem_𝔹_iff] at hP
  rcases hP with rfl | rfl
  · exact and_iff_left_of_imp id
  · constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      nomatch notMem_empty _ h

theorem and_iff (p q : ZFBool) : p ⋀ q = ⊤ ↔ p = ⊤ ∧ q = ⊤ := by
  constructor
  · intro h
    cases q using casesOn with
    | false =>
      rw [and_false] at h
      nomatch true_ne_false h.symm
    | true => exact ⟨and_true p ▸ h, rfl⟩
  · rintro (⟨rfl,rfl⟩)
    rw [and_true]

abbrev and_intro p q := and_iff p q |>.mpr

theorem or_comm (p q : ZFBool) : p ⋁ q = q ⋁ p := by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_union]
  exact Or.comm

theorem or_assoc (p q r : ZFBool) : p ⋁ q ⋁ r = p ⋁ (q ⋁ r) := by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  obtain ⟨R, hR⟩ := r
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_union]
  exact _root_.or_assoc

theorem or_true (p : ZFBool) : p ⋁ ⊤ = ⊤ := by
  obtain ⟨P, hP⟩ := p
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_union]
  rw [mem_𝔹_iff] at hP
  cases hP <;> subst_eqs
  · simp only [notMem_empty, mem_singleton, false_or, top_eq_true]
  · exact or_iff_left_of_imp id

theorem or_false (p : ZFBool) : p ⋁ ⊥ = p := by
  obtain ⟨P, hP⟩ := p
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_union]
  rw [mem_𝔹_iff] at hP
  cases hP <;> subst_eqs
  · rw [or_self]
  · simp only [notMem_empty, _root_.or_false]

theorem or_iff (p q : ZFBool) : p ⋁ q = ⊤ ↔ p = ⊤ ∨ q = ⊤ := by
  constructor
  · intro h
    cases p using casesOn with
    | false =>
      rw [or_comm, or_false] at h
      exact Or.inr h
    | true => exact Or.inl rfl
  · intro h
    rcases h with rfl | rfl
    · rw [or_comm, or_true]
    · rw [or_true]

abbrev or_intro p q := or_iff p q |>.mpr

open Classical in
/-- Conversion of `ZFBool` to `Lean.Bool`. -/
@[expose] def toBool : ZFBool → Bool
  | ⟨b, hb⟩ =>
    if h : b = zftrue then Bool.true
    else if h' : b = zffalse then Bool.false
    else False.elim (by rcases (ZFBool.mem_𝔹_iff b |>.mp hb) <;> contradiction)

theorem toBool_false : toBool ⊥ = Bool.false := by
  rw [toBool]
  split_ifs with h h'
  · nomatch zftrue_ne_zffalse h.symm
  · rfl
  · nomatch h'

theorem toBool_true : toBool ⊤ = Bool.true := by
  rw [toBool]
  split_ifs with h h'
  · rfl
  · nomatch h rfl
  · nomatch h'

theorem toBool_and (p q : ZFBool) : (p ⋀ q).toBool = (p.toBool && q.toBool) := by
  cases p <;> cases q
  · rw [and_false, toBool_false, Bool.false_and]
  · rw [and_true, toBool_true, toBool_false, Bool.false_and]
  · rw [and_false, toBool_true, toBool_false, Bool.and_false]
  · rw [and_true, toBool_true, Bool.true_and]

theorem toBool_or (p q : ZFBool) : (p ⋁ q).toBool = (p.toBool || q.toBool) := by
  cases p <;> cases q
  · rw [or_false, toBool_false, Bool.false_or]
  · rw [or_true, toBool_true, toBool_false, Bool.or_true]
  · rw [or_false, toBool_true, toBool_false, Bool.true_or]
  · rw [or_true, toBool_true, Bool.true_or]

theorem toBool_not (p : ZFBool) : toBool p.not = ¬ p.toBool := by
  cases p
  · rw [not_false_eq_true, toBool_true, toBool_false, Bool.false_eq_true, Bool.coe_sort_true]
    exact _root_.not_false_eq_true.symm
  · rw [not_true_eq_false, toBool_false, toBool_true, Bool.coe_false]
    exact eq_false (fun h => h rfl) |>.symm

theorem not_top_iff_bot {P : ZFBool} : P ≠ ⊤ ↔ P = ⊥ := by
  constructor
  · intro
    cases P <;> trivial
  · intro _ h
    subst P
    injections h
    nomatch zftrue_ne_zffalse h.symm

theorem not_bot_iff_top {P : ZFBool} : P ≠ ⊥ ↔ P = ⊤ := by
  constructor
  · intro
    cases P <;> trivial
  · intro _ h
    subst P
    injections h
    nomatch zftrue_ne_zffalse h

/-- Conversion of `Lean.Bool` to `ZFBool` -/
@[expose] def ofBool : Bool → ZFBool
  | .true  => ⟨zftrue, ZFBool.zftrue_mem_𝔹⟩
  | .false => ⟨zffalse, ZFBool.zffalse_mem_𝔹⟩

theorem mem_ofBool_𝔹 (b : Bool) : (ofBool b).val ∈ 𝔹 := by
  unfold 𝔹
  rcases b <;> simp [ofBool]

theorem sub_ofBool_singleton_𝔹 (b : Bool) : {(ofBool b).val} ⊆ 𝔹 := by
  intro
  rw [mem_singleton]
  rintro rfl
  exact mem_ofBool_𝔹 b

theorem to_Bool_ofBool (b : Bool) : ZFBool.toBool (ofBool b) = b := by
  cases b <;> rw [ofBool, ZFBool.toBool]
  · split_ifs with h
    · nomatch zftrue_ne_zffalse.symm h
    · rfl
    · generalize_proofs
      contradiction
  · split_ifs with h
    · rfl
    · contradiction
    · generalize_proofs
      contradiction

theorem of_Bool_toBool (b : ZFBool) : ofBool b.toBool = b := by
  obtain ⟨b, hb⟩ := b
  rw [ZFBool.toBool, ofBool.eq_def]
  split_ifs with h <;> (first | subst b | contradiction) <;> trivial

theorem ofBool_decide_eq_true_iff {P : Prop} [Decidable P] : ofBool (decide P) = ⊤ ↔ P := by
  constructor
  · intro h
    cases hP : decide P with
    | false =>
      rw [hP] at h
      unfold ofBool at h
      injection h with h
      nomatch zftrue_ne_zffalse h.symm
    | true => exact decide_eq_true_eq.mp hP
  · intro h
    cases hP : decide P with
    | false =>
      rw [Bool.decide_false_iff] at hP
      contradiction
    | true => rfl

theorem ofBool_decide_eq_false_iff {P : Prop} [Decidable P] : ofBool (decide P) = ⊥ ↔ ¬P := by
  constructor
  · intro h
    cases hP : decide P with
    | false => exact decide_eq_false_iff_not.mp hP
    | true =>
      rw [hP] at h
      unfold ofBool at h
      injection h with h
      nomatch zftrue_ne_zffalse h
  · intro h
    cases hP : decide P with
    | false => rfl
    | true =>
      rw [Bool.decide_iff] at hP
      contradiction

@[expose] def equivBool : ZFBool ≃ Bool where
  toFun := toBool
  invFun := ofBool
  left_inv := of_Bool_toBool
  right_inv := to_Bool_ofBool

instance : Coe Bool ZFBool := ⟨ofBool⟩
instance : Coe ZFBool Bool := ⟨toBool⟩

end ZFBool

end Booleans

section AdditionnalLemmas

namespace ZFBool

theorem and_coe (p q : ZFBool) : p ⋀ q = ((p : Bool) && (q : Bool)) := by
  rw [← toBool_and, of_Bool_toBool]
theorem or_coe (p q : ZFBool) : p ⋁ q = ((p : Bool) || (q : Bool)) := by
  rw [← toBool_or, of_Bool_toBool]
theorem not_coe (p : ZFBool) : ZFBool.not p = ¬(p : Bool) := by
  rw [← toBool_not]

theorem and_or_distrib_left (p q r : ZFBool) : p ⋀ (q ⋁ r) = (p ⋀ q) ⋁ (p ⋀ r) := by
  rw [and_coe, or_coe, and_coe, and_coe, or_coe]
  iterate 3 rw [to_Bool_ofBool]
  rw [Bool.and_or_distrib_left]

end ZFBool
end AdditionnalLemmas

/-! ## Transfer to `Bool` and to `Prop`

`ZFBool` is the same type as `Bool`, through `equivBool`, and — classically — the same type as
`Prop`, through `equivProp`. Both readings are available to the `transfer` tactic:

```
example (p q : ZFBool) : p ⋀ q = q ⋀ p := by
  transfer ZFBool → Bool =>
    exact Bool.and_comm p q

example (p q : ZFBool) : p ⋀ q = q ⋀ p := by
  transfer ZFBool → Prop using ZFBool.equivProp =>
    exact and_comm
```

The block is proved in the target type, and closing it closes the goal about `ZFBool`. `Bool` is
the one registered as a `TransferEquiv`: the class takes its target as an `outParam`, so a type
has at most one instance, and the `Prop` reading is asked for with `using ZFBool.equivProp` (or
`transfer ZFBool.equivProp => …`).

`ZFBool` carries no algebraic structure, so nothing comes for free from the `map_…` lemmas of
`TransferAlgebra`: the two constants and the three connectives are stated below, once per
reading. Those about the connectives need `no_index` on their left-hand side, because
`ZFBool.and`, `ZFBool.or` and `ZFBool.not` are abbreviations: indexed as they stand, they would
be unfolded to the underlying set operations and never fire.
-/

section Transfer

namespace ZFBool

/-! ### The coercions

A `ZFBool` read as a proposition is `p.toBool = true`, the coercion to `Bool` followed by the
coercion of a `Bool` to a proposition. Both readings need that to travel, so it is brought back
to an equation in `ZFBool`, which the equivalence at hand is then pushed through. The lemma fires
*before* its subterms are visited: rewriting `p.toBool` into `equivBool p` first would leave a
`Bool` behind, which is what only one of the two readings wants. A coerced `ZFBool` that is not
compared to anything travels to `Bool` only, through `toBool_eq_equivBool` below. -/
@[transfer_simps↓]
theorem toBool_eq_iff (p : ZFBool) (b : Bool) : p.toBool = b ↔ p = ofBool b := by
  constructor
  · rintro rfl
    rw [of_Bool_toBool]
  · rintro rfl
    rw [to_Bool_ofBool]

attribute [transfer_simps] of_Bool_toBool

@[transfer_simps] theorem ofBool_inj (b c : Bool) : ofBool b = ofBool c ↔ b = c := by
  constructor
  · intro h
    rw [← to_Bool_ofBool b, ← to_Bool_ofBool c, h]
  · rintro rfl
    rfl

@[transfer_simps] theorem ofBool_true : ofBool Bool.true = ⊤ := rfl

@[transfer_simps] theorem ofBool_false : ofBool Bool.false = ⊥ := rfl

/-! ### Transfer to `Bool` -/

/-- Equivalence used by the `transfer` tactic to move goals between `ZFBool` and `Bool`. -/
instance : TransferEquiv ZFBool Bool := ⟨equivBool⟩

/-- A `ZFBool` left as a `Bool` is its image under the equivalence. -/
@[transfer_simps] theorem toBool_eq_equivBool (p : ZFBool) : p.toBool = equivBool p := rfl

@[transfer_simps] theorem equivBool_ofBool (b : Bool) : equivBool (ofBool b) = b :=
  to_Bool_ofBool b

@[transfer_simps] theorem equivBool_true : equivBool ZFBool.true = Bool.true := toBool_true

@[transfer_simps] theorem equivBool_false : equivBool ZFBool.false = Bool.false := toBool_false

@[transfer_simps] theorem equivBool_top : equivBool (⊤ : ZFBool) = Bool.true := toBool_true

@[transfer_simps] theorem equivBool_bot : equivBool (⊥ : ZFBool) = Bool.false := toBool_false

@[transfer_simps] theorem equivBool_and (p q : ZFBool) :
    equivBool (no_index (p ⋀ q)) = (equivBool p && equivBool q) := toBool_and p q

@[transfer_simps] theorem equivBool_or (p q : ZFBool) :
    equivBool (no_index (p ⋁ q)) = (equivBool p || equivBool q) := toBool_or p q

@[transfer_simps] theorem equivBool_not (p : ZFBool) :
    equivBool (no_index p.not) = !equivBool p := by
  cases p with
  | false => rw [not_false_eq_true, equivBool_top, equivBool_bot]; rfl
  | true => rw [not_true_eq_false, equivBool_bot, equivBool_top]; rfl

/-! ### Transfer to `Prop`

Classically `Bool` and `Prop` are the same type, so `ZFBool` is `Prop` as well: `equivProp p` is
the proposition `p = ⊤`. Under this reading the connectives of `ZFBool` are the connectives of
`Prop`, and an equation between `ZFBool`s is an equivalence of propositions. -/

/-- The classical equivalence between `ZFBool` and `Prop`: `p` stands for the proposition that
`p` is `⊤`. Not an instance, `Bool` being the registered target of `ZFBool`; pass it explicitly,
as `transfer ZFBool → Prop using ZFBool.equivProp`. -/
@[expose] noncomputable def equivProp : ZFBool ≃ Prop := equivBool.trans Equiv.propEquivBool.symm

theorem equivProp_apply (p : ZFBool) : equivProp p = (p.toBool = Bool.true) := rfl

@[transfer_simps] theorem equivProp_ofBool (b : Bool) : equivProp (ofBool b) ↔ b := by
  rw [equivProp_apply, to_Bool_ofBool]

@[transfer_simps] theorem equivProp_top : equivProp (⊤ : ZFBool) ↔ True :=
  iff_of_true toBool_true trivial

@[transfer_simps] theorem equivProp_bot : equivProp (⊥ : ZFBool) ↔ False := by
  change (⊥ : ZFBool).toBool = Bool.true ↔ False
  rw [toBool_false]
  exact iff_of_false Bool.false_ne_true not_false

@[transfer_simps] theorem equivProp_true : equivProp ZFBool.true ↔ True := equivProp_top

@[transfer_simps] theorem equivProp_false : equivProp ZFBool.false ↔ False := equivProp_bot

@[transfer_simps] theorem equivProp_and (p q : ZFBool) :
    equivProp (no_index (p ⋀ q)) ↔ (equivProp p ∧ equivProp q) := by
  rw [equivProp_apply, equivProp_apply, equivProp_apply, toBool_and, Bool.and_eq_true]

@[transfer_simps] theorem equivProp_or (p q : ZFBool) :
    equivProp (no_index (p ⋁ q)) ↔ (equivProp p ∨ equivProp q) := by
  rw [equivProp_apply, equivProp_apply, equivProp_apply, toBool_or, Bool.or_eq_true]

@[transfer_simps] theorem equivProp_not (p : ZFBool) :
    equivProp (no_index p.not) ↔ ¬ equivProp p := by
  cases p with
  | false => rw [not_false_eq_true, equivProp_top, equivProp_bot]; simp
  | true => rw [not_true_eq_false, equivProp_bot, equivProp_top]; simp

-- An equation between propositions is their equivalence, and this is what an equation between
-- `ZFBool`s becomes once `equivProp` has been pushed through it.
attribute [transfer_simps] eq_iff_iff iff_true true_iff iff_false false_iff

end ZFBool

end Transfer

end ZFSet

end
