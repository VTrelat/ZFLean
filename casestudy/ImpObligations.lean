/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import ZFLean
public import Imp

/-!
# The case study's side conditions under three search configurations

The 30 leaf obligations of `casestudy/Imp.lean`, each stated on its own with its original
hypotheses, are run under three configurations of the search:

* (i) plain `solve_by_elim`: no tagged lemma sets, local hypotheses only;
* (ii) the library's seeds only: the release tactics with every client-tagged seed erased;
* (iii) the release environment: the release tactics with the library's and the client's
  seeds, as at each obligation's site in `Imp.lean`.

The file checks its own counts. An obligation claimed closed is closed by the bare tactic
call; an obligation claimed open is wrapped in `fail_if_success` and then closed by an
explicit proof; the four searches of configuration (ii) that exhaust their heartbeat budget
instead of failing are wrapped in `#guard_msgs` asserting that timeout. `lake build
ImpObligations` therefore certifies the numbers of the paper: 3 of 30 under (i), 5 under
(ii), 29 under (iii), the thirtieth being the weakening step of the assignment case.

The sections appear in the order (i), (iii), (ii), because erasing an attribute is not undone
within a file. The seven obligations of the determinism proof are tested with the four `Cmd`
seeds declared after that proof erased, since those did not exist at its site. Each `L<n>`
comment names the site in `casestudy/Imp.lean`.
-/

open ZFSet ZFSet.Imp

namespace ImpObligations

variable {V : ZFSet}

/-! ## Configuration (i): plain `solve_by_elim`, no seeds — 3 of 30 close -/

section PlainSolveByElim

-- L1 (`Expr.mem_dom_sem_iff`, the `⟦e⟧ₑ.Dom` parameter)
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success solve_by_elim
  exact Expr.sem_is_rel e
-- L2 (`Expr.mem_dom_sem_iff`, the `σ.Dom` parameter)
example {σ : ZFSet} (hσ : σ ∈ Store V) : σ ⊆ V.prod Nat := by
  fail_if_success solve_by_elim
  exact (IsPFunc_of_mem_Store hσ).1
-- L3 (`Cmd.sem`, the `⟦e⟧ₑ.Dom` of the assignment case)
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success solve_by_elim
  exact Expr.sem_is_rel e
-- L4 (`Cmd.sem_assign`, the `⟦e⟧ₑ.Dom` of the statement)
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success solve_by_elim
  exact Expr.sem_is_rel e
-- L5 (`Cmd.sem_assign_isFunc`, the `⟦e⟧ₑ.Dom` of the statement)
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success solve_by_elim
  exact Expr.sem_is_rel e
-- L6 (`Cmd.mem_dom_sem_assign_iff`, the `⟦assign x e⟧ᶜ.Dom` parameter)
example (x : V) (e : Expr V) : ⟦Cmd.assign x e⟧ᶜ ⊆ (Store V).prod (Store V) := by
  fail_if_success solve_by_elim
  exact Cmd.sem_is_rel _
-- L7 (`Cmd.mem_dom_sem_assign_iff`, the `⟦e⟧ₑ.Dom` parameter)
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success solve_by_elim
  exact Expr.sem_is_rel e
-- L8 (`Cmd.not_mem_dom_assign_of_unassigned`, the `σ.Dom` parameter)
example {σ : ZFSet} (hσ : σ ∈ Store V) : σ ⊆ V.prod Nat := by
  fail_if_success solve_by_elim
  exact (IsPFunc_of_mem_Store hσ).1
-- L9 (`Cmd.not_mem_dom_assign_of_unassigned`, the command's `.Dom` parameter)
example (x y : V) :
    ⟦Cmd.assign x (Expr.add (Expr.var y) (Expr.lit 1))⟧ᶜ ⊆ (Store V).prod (Store V) := by
  fail_if_success solve_by_elim
  exact Cmd.sem_is_rel _
-- L10 (`fapply_override_self`, the `@ᶻ` partial-functionality parameter)
example {σ x n A B : ZFSet} (hσ : σ.IsPFunc A B) (hx : x ∈ A) (hn : n ∈ B) :
    (σ[x ↦ n]).IsPFunc A B := by
  fail_if_success solve_by_elim
  exact IsPFunc.override hσ hx hn
-- L11 (`Cmd.sem`, the `@ᶻ⟦e⟧ₑ` of the assignment case)
example (e : Expr V) : ⟦e⟧ₑ.IsPFunc (Store V) Nat := by
  fail_if_success solve_by_elim
  exact Expr.sem_pfunc e
-- L12 (`Cmd.sem_assign`, the `@ᶻ⟦e⟧ₑ` of the statement)
example (e : Expr V) : ⟦e⟧ₑ.IsPFunc (Store V) Nat := by
  fail_if_success solve_by_elim
  exact Expr.sem_pfunc e
-- L13 (the `fapply_composition` example, the `@ᶻ` on the composition)
example (x y : V) (n m : ZFNat) :
    (fcomp ⟦Cmd.assign y (Expr.lit m)⟧ᶜ ⟦Cmd.assign x (Expr.lit n)⟧ᶜ
      (Cmd.sem_assign_lit_isFunc y m) (Cmd.sem_assign_lit_isFunc x n)).IsPFunc
      (Store V) (Store V) := by
  fail_if_success solve_by_elim
  exact IsPFunc_of_composition_IsPFunc
    (is_func_is_pfunc (Cmd.sem_assign_lit_isFunc x n))
    (is_func_is_pfunc (Cmd.sem_assign_lit_isFunc y m))
-- L14 (the `fapply_composition` example, the outer `@ᶻ⟦assign y (lit m)⟧ᶜ`)
example (y : V) (m : ZFNat) : ⟦Cmd.assign y (Expr.lit m)⟧ᶜ.IsPFunc (Store V) (Store V) := by
  fail_if_success solve_by_elim
  exact Cmd.sem_pfunc _
-- L15 (the `fapply_composition` example, the inner `@ᶻ⟦assign x (lit n)⟧ᶜ`)
example (x : V) (n : ZFNat) : ⟦Cmd.assign x (Expr.lit n)⟧ᶜ.IsPFunc (Store V) (Store V) := by
  fail_if_success solve_by_elim
  exact Cmd.sem_pfunc _
-- L16 (`Cmd.sem_seq_eq_fcomp`, the `∘ᶻ` totality parameter for `⟦c₂⟧ᶜ`)
example {c₁ c₂ : Cmd V} (_h₁ : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ)
    (h₂ : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ) : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ := by
  solve_by_elim
-- L17 (`Cmd.sem_seq_eq_fcomp`, the `∘ᶻ` totality parameter for `⟦c₁⟧ᶜ`)
example {c₁ c₂ : Cmd V} (h₁ : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ)
    (_h₂ : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ) : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ := by
  solve_by_elim
-- L18 (the `fapply_composition` example, the `∘ᶻ` totality parameter, outer)
example (y : V) (m : ZFNat) : (Store V).IsFunc (Store V) ⟦Cmd.assign y (Expr.lit m)⟧ᶜ := by
  fail_if_success solve_by_elim
  exact Cmd.sem_assign_lit_isFunc y m
-- L19 (the `fapply_composition` example, the `∘ᶻ` totality parameter, inner)
example (x : V) (n : ZFNat) : (Store V).IsFunc (Store V) ⟦Cmd.assign x (Expr.lit n)⟧ᶜ := by
  fail_if_success solve_by_elim
  exact Cmd.sem_assign_lit_isFunc x n
-- L20 (`fapply_override_self`, the `by zdom` domain proof)
example {σ x n A B : ZFSet} (hσ : σ.IsPFunc A B) (hx : x ∈ A) (hn : n ∈ B) :
    x ∈ (σ[x ↦ n]).Dom (is_rel_of_is_pfunc (IsPFunc.override hσ hx hn)) := by
  fail_if_success solve_by_elim
  exact mem_dom_override_self hσ hx hn
-- L21 (the `fapply_composition` example, the outer `⟨σ, by zdom⟩`)
example (x y : V) (n m : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    σ ∈ (fcomp ⟦Cmd.assign y (Expr.lit m)⟧ᶜ ⟦Cmd.assign x (Expr.lit n)⟧ᶜ
      (Cmd.sem_assign_lit_isFunc y m) (Cmd.sem_assign_lit_isFunc x n)).Dom
      is_rel_of_composition := by
  fail_if_success solve_by_elim
  exact mem_dom_of_mem (IsFunc_of_composition_IsFunc
    (Cmd.sem_assign_lit_isFunc y m) (Cmd.sem_assign_lit_isFunc x n)) hσ
-- L22 (the `fapply_composition` example, the middle `⟨…, by zdom⟩` on the applied value)
example (x y : V) (n m : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    (fapply ⟦Cmd.assign x (Expr.lit n)⟧ᶜ (is_func_is_pfunc (Cmd.sem_assign_lit_isFunc x n))
      ⟨σ, mem_dom_of_mem (Cmd.sem_assign_lit_isFunc x n) hσ⟩).val
      ∈ ⟦Cmd.assign y (Expr.lit m)⟧ᶜ.Dom (Cmd.sem_is_rel _) := by
  fail_if_success solve_by_elim
  exact mem_dom_of_mem (Cmd.sem_assign_lit_isFunc y m)
    (fapply_mem_range (is_func_is_pfunc (Cmd.sem_assign_lit_isFunc x n)) _)
-- L23 (the `fapply_composition` example, the inner `⟨σ, by zdom⟩`)
example (x : V) (n : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    σ ∈ ⟦Cmd.assign x (Expr.lit n)⟧ᶜ.Dom (Cmd.sem_is_rel _) := by
  fail_if_success solve_by_elim
  exact mem_dom_of_mem (Cmd.sem_assign_lit_isFunc x n) hσ
-- L24 (`Cmd.sem_pfunc`, the skip case)
example : (𝟙(Store V)).IsPFunc (Store V) (Store V) := by
  fail_if_success solve_by_elim
  exact Id.IsPFunc
-- L25 (`Cmd.sem_pfunc`, the seq case)
example {c₁ c₂ : Cmd V} (ih₁ : ⟦c₁⟧ᶜ.IsPFunc (Store V) (Store V))
    (ih₂ : ⟦c₂⟧ᶜ.IsPFunc (Store V) (Store V)) :
    (composition ⟦c₂⟧ᶜ ⟦c₁⟧ᶜ (Store V) (Store V) (Store V)).IsPFunc (Store V) (Store V) := by
  fail_if_success solve_by_elim
  exact IsPFunc_of_composition_IsPFunc ih₁ ih₂
-- L26 (`Cmd.sem_pfunc`, the whileDo case)
example (e : Expr V) {c : Cmd V} (ih : ⟦c⟧ᶜ.IsPFunc (Store V) (Store V))
    (hd : ∀ σ : ZFSet, σ ∈ e.tt → σ ∈ e.ff → False) :
    (loop (Store V) e.tt e.ff ⟦c⟧ᶜ).IsPFunc (Store V) (Store V) := by
  fail_if_success solve_by_elim
  exact loop_pfunc ih hd
-- L27 (`Cmd.sem_pfunc`, the ite case: first premise of the union rule)
example (e : Expr V) {c₁ : Cmd V} (ih₁ : ⟦c₁⟧ᶜ.IsPFunc (Store V) (Store V)) :
    (e.tt ◁ ⟦c₁⟧ᶜ).IsPFunc (Store V) (Store V) := by
  fail_if_success solve_by_elim
  exact IsPFunc.domRestrict ih₁
-- L28 (`Cmd.sem_pfunc`, the ite case: second premise of the union rule)
example (e : Expr V) {c₂ : Cmd V} (ih₂ : ⟦c₂⟧ᶜ.IsPFunc (Store V) (Store V)) :
    (e.ff ◁ ⟦c₂⟧ᶜ).IsPFunc (Store V) (Store V) := by
  fail_if_success solve_by_elim
  exact IsPFunc.domRestrict ih₂
-- L29 (`Cmd.sem_pfunc`, the ite case: the disjointness premise of the union rule)
example (e : Expr V) {c₁ c₂ : Cmd V}
    (hd : ∀ σ τ τ' : ZFSet, σ.pair τ ∈ e.tt ◁ ⟦c₁⟧ᶜ → σ.pair τ' ∈ e.ff ◁ ⟦c₂⟧ᶜ → False) :
    ∀ x y z : ZFSet, x.pair y ∈ e.tt ◁ ⟦c₁⟧ᶜ → x.pair z ∈ e.ff ◁ ⟦c₂⟧ᶜ → False := by
  solve_by_elim
-- L30 (`Cmd.sem_pfunc`, the assignment case — the manual weakening step)
example (x : V) (e : Expr V) : ⟦Cmd.assign x e⟧ᶜ.IsPFunc (Store V) (Store V) := by
  fail_if_success solve_by_elim
  rw [Cmd.sem_assign]
  exact pfunc_weaken lambda_isPFunc (dom_subset _ _) fun _ h => h

end PlainSolveByElim

/-! ## Configuration (iii): the full environment — 29 of 30 close by one invocation -/

section FullEnvironment

-- L1–L9: the nine relation obligations, `zrel`
-- L1
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by zrel
-- L2
example {σ : ZFSet} (hσ : σ ∈ Store V) : σ ⊆ V.prod Nat := by zrel
-- L3
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by zrel
-- L4
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by zrel
-- L5
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by zrel
-- L6
example (x : V) (e : Expr V) : ⟦Cmd.assign x e⟧ᶜ ⊆ (Store V).prod (Store V) := by zrel
-- L7
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by zrel
-- L8
example {σ : ZFSet} (hσ : σ ∈ Store V) : σ ⊆ V.prod Nat := by zrel
-- L9
example (x y : V) :
    ⟦Cmd.assign x (Expr.add (Expr.var y) (Expr.lit 1))⟧ᶜ ⊆ (Store V).prod (Store V) := by zrel

-- L10–L15: the six `@ᶻ` partial-functionality obligations, `zpfun`
-- L10
example {σ x n A B : ZFSet} (hσ : σ.IsPFunc A B) (hx : x ∈ A) (hn : n ∈ B) :
    (σ[x ↦ n]).IsPFunc A B := by zpfun
-- L11
example (e : Expr V) : ⟦e⟧ₑ.IsPFunc (Store V) Nat := by zpfun
-- L12
example (e : Expr V) : ⟦e⟧ₑ.IsPFunc (Store V) Nat := by zpfun
-- L13
example (x y : V) (n m : ZFNat) :
    (fcomp ⟦Cmd.assign y (Expr.lit m)⟧ᶜ ⟦Cmd.assign x (Expr.lit n)⟧ᶜ
      (Cmd.sem_assign_lit_isFunc y m) (Cmd.sem_assign_lit_isFunc x n)).IsPFunc
      (Store V) (Store V) := by zpfun
-- L14
example (y : V) (m : ZFNat) :
    ⟦Cmd.assign y (Expr.lit m)⟧ᶜ.IsPFunc (Store V) (Store V) := by zpfun
-- L15
example (x : V) (n : ZFNat) :
    ⟦Cmd.assign x (Expr.lit n)⟧ᶜ.IsPFunc (Store V) (Store V) := by zpfun

-- L16–L19: the four `∘ᶻ` totality obligations, `zfun`
-- L16
example {c₁ c₂ : Cmd V} (_h₁ : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ)
    (h₂ : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ) : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ := by zfun
-- L17
example {c₁ c₂ : Cmd V} (h₁ : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ)
    (_h₂ : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ) : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ := by zfun
-- L18
example (y : V) (m : ZFNat) : (Store V).IsFunc (Store V) ⟦Cmd.assign y (Expr.lit m)⟧ᶜ := by -- L18
  zfun
-- L19
example (x : V) (n : ZFNat) : (Store V).IsFunc (Store V) ⟦Cmd.assign x (Expr.lit n)⟧ᶜ := by -- L19
  zfun

-- L20–L23: the four `by zdom` domain proofs
-- L20
example {σ x n A B : ZFSet} (hσ : σ.IsPFunc A B) (hx : x ∈ A) (hn : n ∈ B) :
    x ∈ (σ[x ↦ n]).Dom (is_rel_of_is_pfunc (IsPFunc.override hσ hx hn)) := by zdom
-- L21
example (x y : V) (n m : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    σ ∈ (fcomp ⟦Cmd.assign y (Expr.lit m)⟧ᶜ ⟦Cmd.assign x (Expr.lit n)⟧ᶜ
      (Cmd.sem_assign_lit_isFunc y m) (Cmd.sem_assign_lit_isFunc x n)).Dom
      is_rel_of_composition := by zdom
-- L22
example (x y : V) (n m : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    (fapply ⟦Cmd.assign x (Expr.lit n)⟧ᶜ (is_func_is_pfunc (Cmd.sem_assign_lit_isFunc x n))
      ⟨σ, mem_dom_of_mem (Cmd.sem_assign_lit_isFunc x n) hσ⟩).val
      ∈ ⟦Cmd.assign y (Expr.lit m)⟧ᶜ.Dom (Cmd.sem_is_rel _) := by zdom
-- L23
example (x : V) (n : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    σ ∈ ⟦Cmd.assign x (Expr.lit n)⟧ᶜ.Dom (Cmd.sem_is_rel _) := by zdom

end FullEnvironment

/- The seven obligations of the determinism proof are tested without the four `Cmd` seeds
declared after that proof, which did not exist at its site. -/
attribute [-zpfun] ZFSet.Imp.Cmd.sem_pfunc
attribute [-zrel] ZFSet.Imp.Cmd.sem_is_rel
attribute [-zfun] ZFSet.Imp.Cmd.sem_assign_lit_isFunc ZFSet.Imp.Cmd.sem_seq_isFunc

section FullEnvironmentDetProof

-- L24–L29: the six `zpfun`-closed goals of the determinism proof
-- L24
example : (𝟙(Store V)).IsPFunc (Store V) (Store V) := by zpfun
-- L25
example {c₁ c₂ : Cmd V} (ih₁ : ⟦c₁⟧ᶜ.IsPFunc (Store V) (Store V))
    (ih₂ : ⟦c₂⟧ᶜ.IsPFunc (Store V) (Store V)) :
    (composition ⟦c₂⟧ᶜ ⟦c₁⟧ᶜ (Store V) (Store V) (Store V)).IsPFunc (Store V) (Store V) := by
  zpfun
-- L26
example (e : Expr V) {c : Cmd V} (ih : ⟦c⟧ᶜ.IsPFunc (Store V) (Store V))
    (hd : ∀ σ : ZFSet, σ ∈ e.tt → σ ∈ e.ff → False) :
    (loop (Store V) e.tt e.ff ⟦c⟧ᶜ).IsPFunc (Store V) (Store V) := by zpfun
-- L27
example (e : Expr V) {c₁ : Cmd V} (ih₁ : ⟦c₁⟧ᶜ.IsPFunc (Store V) (Store V)) :
    (e.tt ◁ ⟦c₁⟧ᶜ).IsPFunc (Store V) (Store V) := by zpfun
-- L28
example (e : Expr V) {c₂ : Cmd V} (ih₂ : ⟦c₂⟧ᶜ.IsPFunc (Store V) (Store V)) :
    (e.ff ◁ ⟦c₂⟧ᶜ).IsPFunc (Store V) (Store V) := by zpfun
-- L29
example (e : Expr V) {c₁ c₂ : Cmd V}
    (hd : ∀ σ τ τ' : ZFSet, σ.pair τ ∈ e.tt ◁ ⟦c₁⟧ᶜ → σ.pair τ' ∈ e.ff ◁ ⟦c₂⟧ᶜ → False) :
    ∀ x y z : ZFSet, x.pair y ∈ e.tt ◁ ⟦c₁⟧ᶜ → x.pair z ∈ e.ff ◁ ⟦c₂⟧ᶜ → False := by zpfun
-- L30: the assignment case — `zpfun` has no weakening rule; `pfunc_weaken` is the manual step
-- L30
example (x : V) (e : Expr V) : ⟦Cmd.assign x e⟧ᶜ.IsPFunc (Store V) (Store V) := by
  fail_if_success zpfun
  rw [Cmd.sem_assign]
  exact pfunc_weaken lambda_isPFunc (dom_subset _ _) fun _ h => h

end FullEnvironmentDetProof

/-! ## Configuration (ii): the library's seeds only — every client-tagged seed erased -/

attribute [-zrel] ZFSet.domRestrict_is_rel ZFSet.override_is_rel ZFSet.union_is_rel
  ZFSet.loopIter_is_rel ZFSet.loop_is_rel ZFSet.Imp.Expr.sem_is_rel
attribute [-zpfun] ZFSet.IsPFunc.domRestrict ZFSet.IsPFunc.override ZFSet.IsPFunc.union
  ZFSet.IsPFunc.empty ZFSet.loop_pfunc ZFSet.lambda_isPFunc ZFSet.Imp.IsPFunc_of_mem_Store
  ZFSet.Imp.Expr.sem_pfunc
attribute [-zdom] ZFSet.mem_dom_override_self
attribute [-zfun] ZFSet.Imp.Expr.sem_lit_isFunc

section LibraryCoreOnly

-- L1–L9: `zrel` — every relation obligation concerns a client construction
-- L1
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success zrel
  exact Expr.sem_is_rel e
-- L2
example {σ : ZFSet} (hσ : σ ∈ Store V) : σ ⊆ V.prod Nat := by
  fail_if_success zrel
  exact (IsPFunc_of_mem_Store hσ).1
-- L3
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success zrel
  exact Expr.sem_is_rel e
-- L4
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success zrel
  exact Expr.sem_is_rel e
-- L5
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success zrel
  exact Expr.sem_is_rel e
-- L6
example (x : V) (e : Expr V) : ⟦Cmd.assign x e⟧ᶜ ⊆ (Store V).prod (Store V) := by
  fail_if_success zrel
  exact Cmd.sem_is_rel _
-- L7
example (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  fail_if_success zrel
  exact Expr.sem_is_rel e
-- L8
example {σ : ZFSet} (hσ : σ ∈ Store V) : σ ⊆ V.prod Nat := by
  fail_if_success zrel
  exact (IsPFunc_of_mem_Store hσ).1
-- L9
example (x y : V) :
    ⟦Cmd.assign x (Expr.add (Expr.var y) (Expr.lit 1))⟧ᶜ ⊆ (Store V).prod (Store V) := by
  fail_if_success zrel
  exact Cmd.sem_is_rel _

-- L10–L15: `zpfun`
-- L10
example {σ x n A B : ZFSet} (hσ : σ.IsPFunc A B) (hx : x ∈ A) (hn : n ∈ B) :
    (σ[x ↦ n]).IsPFunc A B := by
  fail_if_success zpfun
  exact IsPFunc.override hσ hx hn
-- L11
example (e : Expr V) : ⟦e⟧ₑ.IsPFunc (Store V) Nat := by
  fail_if_success zpfun
  exact Expr.sem_pfunc e
-- L12
example (e : Expr V) : ⟦e⟧ₑ.IsPFunc (Store V) Nat := by
  fail_if_success zpfun
  exact Expr.sem_pfunc e
-- L13
example (x y : V) (n m : ZFNat) :
    (fcomp ⟦Cmd.assign y (Expr.lit m)⟧ᶜ ⟦Cmd.assign x (Expr.lit n)⟧ᶜ
      (Cmd.sem_assign_lit_isFunc y m) (Cmd.sem_assign_lit_isFunc x n)).IsPFunc
      (Store V) (Store V) := by
  fail_if_success zpfun
  exact IsPFunc_of_composition_IsPFunc
    (is_func_is_pfunc (Cmd.sem_assign_lit_isFunc x n))
    (is_func_is_pfunc (Cmd.sem_assign_lit_isFunc y m))
-- L14
example (y : V) (m : ZFNat) :
    ⟦Cmd.assign y (Expr.lit m)⟧ᶜ.IsPFunc (Store V) (Store V) := by
  fail_if_success zpfun
  exact is_func_is_pfunc (Cmd.sem_assign_lit_isFunc y m)
-- L15
example (x : V) (n : ZFNat) :
    ⟦Cmd.assign x (Expr.lit n)⟧ᶜ.IsPFunc (Store V) (Store V) := by
  fail_if_success zpfun
  exact is_func_is_pfunc (Cmd.sem_assign_lit_isFunc x n)

-- L16–L19: `zfun` — the two hypothesis-shaped obligations survive; the client rules do not
-- L16
example {c₁ c₂ : Cmd V} (_h₁ : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ)
    (h₂ : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ) : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ := by zfun
-- L17
example {c₁ c₂ : Cmd V} (h₁ : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ)
    (_h₂ : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ) : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ := by zfun
-- L18
example (y : V) (m : ZFNat) :
    (Store V).IsFunc (Store V) ⟦Cmd.assign y (Expr.lit m)⟧ᶜ := by
  fail_if_success zfun
  exact Cmd.sem_assign_lit_isFunc y m
-- L19
example (x : V) (n : ZFNat) :
    (Store V).IsFunc (Store V) ⟦Cmd.assign x (Expr.lit n)⟧ᶜ := by
  fail_if_success zfun
  exact Cmd.sem_assign_lit_isFunc x n

-- L20–L23: `zdom`
-- L20: without the client seeds the search exhausts a doubled heartbeat budget instead of
-- failing; `#guard_msgs` asserts that. The message names the routine the budget ran out in
-- (`whnf`, `isDefEq`, …), which is not stable across builds; `debug.moduleNameAtTimeout false`
-- drops that name, as Lean's own test suite does, and leaves the timeout itself asserted.
/--
error: (deterministic) timeout, maximum number of heartbeats (400000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option debug.moduleNameAtTimeout false in
set_option maxHeartbeats 400000 in
example {σ x n A B : ZFSet} (hσ : σ.IsPFunc A B) (hx : x ∈ A) (hn : n ∈ B) :
    x ∈ (σ[x ↦ n]).Dom (is_rel_of_is_pfunc (IsPFunc.override hσ hx hn)) := by
  zdom
-- L21 — same budget exhaustion.
/--
error: (deterministic) timeout, maximum number of heartbeats (400000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option debug.moduleNameAtTimeout false in
set_option maxHeartbeats 400000 in
example (x y : V) (n m : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    σ ∈ (fcomp ⟦Cmd.assign y (Expr.lit m)⟧ᶜ ⟦Cmd.assign x (Expr.lit n)⟧ᶜ
      (Cmd.sem_assign_lit_isFunc y m) (Cmd.sem_assign_lit_isFunc x n)).Dom
      is_rel_of_composition := by
  zdom
-- L22 — same budget exhaustion.
/--
error: (deterministic) timeout, maximum number of heartbeats (400000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option debug.moduleNameAtTimeout false in
set_option maxHeartbeats 400000 in
example (x y : V) (n m : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    (fapply ⟦Cmd.assign x (Expr.lit n)⟧ᶜ (is_func_is_pfunc (Cmd.sem_assign_lit_isFunc x n))
      ⟨σ, mem_dom_of_mem (Cmd.sem_assign_lit_isFunc x n) hσ⟩).val
      ∈ ⟦Cmd.assign y (Expr.lit m)⟧ᶜ.Dom (Cmd.sem_is_rel _) := by
  zdom
-- L23 — same budget exhaustion.
/--
error: (deterministic) timeout, maximum number of heartbeats (400000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option debug.moduleNameAtTimeout false in
set_option maxHeartbeats 400000 in
example (x : V) (n : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    σ ∈ ⟦Cmd.assign x (Expr.lit n)⟧ᶜ.Dom (Cmd.sem_is_rel _) := by
  zdom

-- L24–L30: the determinism-proof goals — identity and composition survive on library rules
-- L24
example : (𝟙(Store V)).IsPFunc (Store V) (Store V) := by zpfun
-- L25
example {c₁ c₂ : Cmd V} (ih₁ : ⟦c₁⟧ᶜ.IsPFunc (Store V) (Store V))
    (ih₂ : ⟦c₂⟧ᶜ.IsPFunc (Store V) (Store V)) :
    (composition ⟦c₂⟧ᶜ ⟦c₁⟧ᶜ (Store V) (Store V) (Store V)).IsPFunc (Store V) (Store V) := by
  zpfun
-- L26
example (e : Expr V) {c : Cmd V} (ih : ⟦c⟧ᶜ.IsPFunc (Store V) (Store V))
    (hd : ∀ σ : ZFSet, σ ∈ e.tt → σ ∈ e.ff → False) :
    (loop (Store V) e.tt e.ff ⟦c⟧ᶜ).IsPFunc (Store V) (Store V) := by
  fail_if_success zpfun
  exact loop_pfunc ih hd
-- L27
example (e : Expr V) {c₁ : Cmd V} (ih₁ : ⟦c₁⟧ᶜ.IsPFunc (Store V) (Store V)) :
    (e.tt ◁ ⟦c₁⟧ᶜ).IsPFunc (Store V) (Store V) := by
  fail_if_success zpfun
  exact IsPFunc.domRestrict ih₁
-- L28
example (e : Expr V) {c₂ : Cmd V} (ih₂ : ⟦c₂⟧ᶜ.IsPFunc (Store V) (Store V)) :
    (e.ff ◁ ⟦c₂⟧ᶜ).IsPFunc (Store V) (Store V) := by
  fail_if_success zpfun
  exact IsPFunc.domRestrict ih₂
-- L29
example (e : Expr V) {c₁ c₂ : Cmd V}
    (hd : ∀ σ τ τ' : ZFSet, σ.pair τ ∈ e.tt ◁ ⟦c₁⟧ᶜ → σ.pair τ' ∈ e.ff ◁ ⟦c₂⟧ᶜ → False) :
    ∀ x y z : ZFSet, x.pair y ∈ e.tt ◁ ⟦c₁⟧ᶜ → x.pair z ∈ e.ff ◁ ⟦c₂⟧ᶜ → False := by zpfun
-- L30
example (x : V) (e : Expr V) : ⟦Cmd.assign x e⟧ᶜ.IsPFunc (Store V) (Store V) := by
  fail_if_success zpfun
  rw [Cmd.sem_assign]
  exact pfunc_weaken lambda_isPFunc (dom_subset _ _) fun _ h => h

end LibraryCoreOnly

end ImpObligations
