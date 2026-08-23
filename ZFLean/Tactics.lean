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
/- Converse-shaped membership lemmas (`x ∈ f.Dom → x ∈ A`). Kept out of the main `zdom` seed set:
together with `mem_dom_of_mem` they let the search loop between `x ∈ A` and `x ∈ f.Dom`, which
exhausts the heartbeat budget whenever the membership fact is not a local hypothesis. They are
tried only in a second, fallback search. -/
register_label_attr zdom_conv

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

macro "zrel" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zrel, zpfun, zfun)

set_option hygiene false in
macro "zpfun" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zpfun, zfun)

set_option hygiene false in
macro "zfun" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zfun)

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

The converse lemmas (`zdom_conv`, e.g. `mem_of_mem_dom : x ∈ f.Dom → x ∈ A`) are tried only in a
second search: in the main one they would let `solve_by_elim` loop between `x ∈ A` and
`x ∈ f.Dom` before it reaches `Subtype.property` or `pair_mem_prod_of_mem`, and time out.
-/
set_option hygiene false in
macro "zdom" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zdom, zfun, zpfun
  | solve_by_elim using zdom, zdom_conv, zfun, zpfun)
end ZFTactics

end
