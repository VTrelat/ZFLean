/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public meta import Lean.LabelAttribute
public import Lean.LabelAttribute
-- re-exported: the macros below expand to `sorry_if_sorry` at the *use* site, so the
-- tactic has to be in scope wherever `zrel`/`zpfun`/`zfun`/`zdom` are called.
public import Mathlib.CategoryTheory.Category.Basic
import ZFLean.Transfer

/-!
# Custom tactics for ZF

This file registers label attributes and defines the `zrel`, `zpfun`, `zfun`, and `zdom`
tactics used to discharge relation, partial-function, function, and domain-membership side
goals.
-/

public meta section

register_label_attr zrel
register_label_attr zpfun
register_label_attr zfun
register_label_attr zdom
/- Membership in a function space is an *equivalence* with `IsFunc` (`ZFSet.mem_funs`), so neither
direction can be a seed: with `mem_funs_of_is_func` they would close a cycle inside `zdom`'s
search. Each tactic instead takes one forward step first, adding to the context the `IsFunc`
consequence of a function-space membership hypothesis. Rewriting that hypothesis in place
(`simp only [ZFSet.mem_funs] at *`) does *not* work: at a `@ᶻ` site the goal `x ∈ Dom f ⋯` carries
a proof term mentioning the hypothesis, so `simp at *` skips it as dependent and reports no
progress. Adding a new hypothesis sidesteps that, and cannot cycle. -/

/- The converse-shaped membership lemma `mem_of_mem_dom : x ∈ f.Dom → x ∈ A` is not a seed:
together with `mem_dom_of_mem` it lets the search loop between `x ∈ A` and `x ∈ f.Dom`, and a
loop through a goal whose function is still a metavariable exhausts the heartbeat budget instead
of failing. `zdom` applies it once instead, as a fallback step (see the macro below). -/

/-!
Thanks to Ghilain for the idea of registering specific attributes
-/
namespace ZFTactics
set_option hygiene false

-- `sorry_if_sorry` (Mathlib, `Mathlib/CategoryTheory/Category/Basic.lean`) closes the main goal
-- with `sorry` when the goal's type already *contains* a `sorry`, and fails otherwise. It is the
-- first branch of each `first | …` so that goals already poisoned by an upstream `sorry` are
-- discharged instantly instead of sending `solve_by_elim` on a hopeless search. In the released
-- 0-sorry artifact it never fires; it only matters while a development is in progress.

-- Every search runs under `with_reducible`. The seeds' conclusions are membership and
-- well-formedness statements about `sep`, `prod`, `powerset`, `funs`, `lambda`, … ; at default
-- transparency a *failing* unification of a seed against a goal unfolds these down to the
-- quotient construction of the model before giving up, and a client that tags a few seeds of
-- its own (see `casestudy/Imp.lean`) pushes `zdom` over the heartbeat budget through failures
-- alone. At reducible transparency the same searches close the same sites in the library, the
-- mismatches fail on the head symbol, and the case-study module elaborates twice as fast.

macro "zrel" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | (have := ZFSet.mem_funs.mp ‹_ ∈ ZFSet.funs _ _›
     with_reducible solve_by_elim using zrel, zpfun, zfun)
  | with_reducible solve_by_elim using zrel, zpfun, zfun)

set_option hygiene false in
macro "zpfun" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | (have := ZFSet.mem_funs.mp ‹_ ∈ ZFSet.funs _ _›; with_reducible solve_by_elim using zpfun, zfun)
  | with_reducible solve_by_elim using zpfun, zfun)

set_option hygiene false in
macro "zfun" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | (have := ZFSet.mem_funs.mp ‹_ ∈ ZFSet.funs _ _›; with_reducible solve_by_elim using zfun)
  | with_reducible solve_by_elim using zfun)

/-
`zdom` discharges the membership side conditions that show up at function-application sites:
`x ∈ f.Dom`, the `x ∈ A` and `(@ᶻf ⟨x, _⟩).val ∈ B` goals that feed them, and the
`pair`/`funs`/`powerset` membership goals of the same shape.

It searches with the `zdom` seed lemmas together with the `zfun` and `zpfun` sets, because the
seeds carry `IsFunc`/`IsPFunc` hypotheses (`mem_dom_of_mem`, `mem_funs_of_is_func`,
`fapply_mem_range`, `mem_of_mem_dom`). The `zrel` set is not searched: no seed produces a
relation-shaped subgoal, and a build with `zrel` added closes exactly the same sites. Note that
`is_func_dom_eq` itself is an *equation*, hence invisible to `solve_by_elim`; the membership
bridge `mem_dom_of_mem` (`ZFLean/Functions.lean`) is what makes `x ∈ f.Dom` reachable.

The converse lemma `mem_of_mem_dom : x ∈ f.Dom → x ∈ A` is not searched: in the main search it
would let `solve_by_elim` loop between `x ∈ A` and `x ∈ f.Dom` before it reaches
`Subtype.property` or `pair_mem_prod_of_mem`, and a search in which the function is a
metavariable does not fail, it times out. The fallback applies it once, with its membership
premise taken from a hypothesis or a subtype binder, and searches only the `IsPFunc` premise,
whose function is then known. When every step fails, the error names the tactic.
-/
set_option hygiene false in
macro "zdom" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | (have := ZFSet.mem_funs.mp ‹_ ∈ ZFSet.funs _ _›
     with_reducible solve_by_elim using zdom, zfun, zpfun)
  | with_reducible solve_by_elim using zdom, zfun, zpfun
  | (refine ZFSet.mem_of_mem_dom ?_ (by first | assumption | exact Subtype.property _)
     first
     | (have := ZFSet.mem_funs.mp ‹_ ∈ ZFSet.funs _ _›
        with_reducible solve_by_elim using zpfun, zfun)
     | with_reducible solve_by_elim using zpfun, zfun)
  | fail "zdom: no seed closes this membership goal")
end ZFTactics

end
