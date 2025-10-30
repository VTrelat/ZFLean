import ZFLean.Basic
import Mathlib.SetTheory.ZFC.Class
import Mathlib.Algebra.Ring.Basic
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Ring
import Mathlib.Data.Finite.Defs
-- import Extra.Utils

noncomputable section

namespace ZFSet

section Preamble

@[simp] theorem not_nonempty_is_empty {x : ZFSet} : ¬ x.Nonempty ↔ x = ∅ := by
  rw [nonempty_def, not_exists, eq_empty]

theorem insert_def {x y : ZFSet} : insert x y = {x} ∪ y := by
  ext1 z
  rw [mem_insert_iff, mem_union, mem_singleton]

/--
A set `x` is transitive if every element of `x` is a subset of `x`:
`∀ y ∈ x, y ⊆ x`.
-/
def transitive (x : ZFSet) := ∀ y ∈ x, y ⊆ x

notation "ω" => omega

/--
An inductive set is defined as a set that contains the empty set `∅` and is closed
under successor.

*The "successor" of a set `x` is defined as the insertion of `x` into itself.*
-/
def inductive_set (E : ZFSet) : Prop := ∅ ∈ E ∧ ∀ n, n ∈ E → insert n n ∈ E

lemma prod_nonempty {x y} : x ≠ ∅ → y ≠ ∅ → ZFSet.prod x y ≠ ∅ := by classical
  intro hx hy h'
  simp only [ZFSet.ext_iff, ZFSet.mem_prod, ZFSet.notMem_empty,
    iff_false, not_exists, not_and, not_forall] at h'
  obtain ⟨a, ha⟩ := nonempty_exists_iff.mp hx
  obtain ⟨b, hb⟩ := nonempty_exists_iff.mp hy
  obtain ⟨_, h'⟩ := h' (a.pair b) _ ha _ hb
  exact h' (Eq.to_iff rfl)

theorem trans_imp_insert_trans {x : ZFSet} : transitive x → transitive (insert x x) := by
  intro trans y
  rw [mem_insert_iff]
  rintro ⟨rfl | _⟩
  · simp_rw [subset_def, mem_insert_iff]
    exact fun _ ↦ Or.inr
  · simp_rw [subset_def, mem_insert_iff]
    exact fun _ _ => Or.inr (trans y ‹_› ‹_›)

theorem inductive_sep {S} (P : ZFSet → Prop)
  (ind : inductive_set S) (h₀ : P ∅) (h₁ : ∀ n ∈ S, P n → P (insert n n)) :
    inductive_set <| S.sep P := by
  unfold inductive_set at *
  simp_rw [mem_sep]
  apply And.intro
  · exact ⟨ind.left, h₀⟩
  · rintro n ⟨_,_⟩
    apply And.intro
    · exact ind.right n ‹_›
    · exact h₁ n ‹_› ‹_›

theorem inductive_imp_transitive {E : ZFSet} :
    inductive_set E → inductive_set (E.sep transitive) := by
  unfold inductive_set
  rintro ⟨_, hind⟩
  apply And.intro <;> simp_rw [mem_sep]
  · exact ⟨‹_›, by intro; rw [imp_iff_or_not]; exact Or.inr <| notMem_empty _⟩
  · rintro n ⟨_,_⟩
    apply And.intro
    · exact hind n ‹_›
    · exact trans_imp_insert_trans ‹_›

theorem insert_mem {x y : ZFSet} (h : x ∈ y) : insert x y = y := by
  ext1
  rw [mem_insert_iff, or_iff_right_iff_imp]
  rintro rfl
  trivial

/--
The first Von Neumann ordinal `ω` is an inductive set.
-/
theorem omega_inductive : inductive_set ω := ⟨omega_zero, fun _ ↦ omega_succ⟩

/--
Witness for an infinite set, meant to be used for definitional purpose only.
-/
private abbrev some_inf := @Classical.choose _ inductive_set ⟨_, omega_inductive⟩

/--
The set `some_inf` is inductive.
-/
private lemma inductive_some_inf : inductive_set some_inf := Classical.choose_spec _
private lemma some_inf_nonempty : some_inf ≠ ∅ := by
  intro h
  let h' := inductive_some_inf.left
  rw [h] at h'
  exact (ZFSet.notMem_empty ∅) h'
private lemma some_inf_mem_sep_inductive_set : some_inf ∈ some_inf.powerset.sep inductive_set := by
  simp only [mem_sep, mem_powerset, subset_refl, true_and]
  exact inductive_some_inf

def symmDiff (p q : ZFSet) : ZFSet := (p \ q) ∪ (q \ p)
infix:70 " Δ " => symmDiff

@[simp]
theorem mem_symmDiff (x p q : ZFSet) : x ∈ p Δ q ↔ (x ∈ p ∧ x ∉ q) ∨ (x ∈ q ∧ x ∉ p) := by
  simp only [symmDiff, mem_union, mem_diff]

@[simp]
theorem symmDiff_empty (p : ZFSet) : p Δ ∅ = p := by
  ext x
  simp only [mem_symmDiff, notMem_empty, not_false_eq_true, and_true, false_and, or_false]

theorem symmDiff_comm (p q : ZFSet) : p Δ q = q Δ p := by
  ext x
  simp only [mem_symmDiff]
  exact Or.comm

@[simp]
theorem symmDiff_self (p : ZFSet) : p Δ p = ∅ := by
  ext x
  simp only [mem_symmDiff, and_not_self, or_self, notMem_empty]

instance ZFSetSProdinst : SProd ZFSet ZFSet ZFSet := ⟨prod⟩

theorem epsilon_mem {y : ZFSet} (hy : y ≠ ∅) : ε y ∈ y := by
  apply ZFSet.choice_mem_aux {y}
  · rw [ZFSet.mem_singleton]
    symm at hy
    exact hy
  · exact ZFSet.mem_singleton.mpr rfl

theorem union_mono {x y z : ZFSet} :  x ⊆ z → y ⊆ z → x ∪ y ⊆ z := by
  intro hx hy a ha
  rw [ZFSet.mem_union] at ha
  rcases ha with _ | _
  · exact hx ‹_›
  · exact hy ‹_›

theorem inter_mono {x y z : ZFSet} :  x ⊆ z → y ⊆ z → x ∩ y ⊆ z := by
  intro hx hy a ha
  rw [ZFSet.mem_inter] at ha
  exact hx ha.1

end Preamble

end ZFSet
end
