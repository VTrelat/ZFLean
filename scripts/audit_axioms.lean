/-
Axiom audit of ZFLean.

Run with `lake env lean scripts/audit_axioms.lean` (after `lake build`, which also builds the
case study `casestudy/Imp.lean`, target `Imp`).

Part 1 prints the axioms of the headline results named in the paper; every line must list at
most `propext`, `Classical.choice` and `Quot.sound`.

Part 2 is exhaustive: it walks every declaration of the `ZFLean` and `Imp` modules and fails
if any depends on an axiom outside those three (`sorryAx` included).
-/
import Lean.Util.CollectAxioms
import ZFLean
import Imp

/-! ## Part 1 — the headline results of the paper -/

-- Relational calculus and function application
#print axioms ZFSet.is_func_ext_iff
#print axioms ZFSet.fapply_lambda
#print axioms ZFSet.fapply_composition
-- Embeddings and isomorphisms: Cantor–Schröder–Bernstein, currying
#print axioms ZFSet.isIso_of_biembedding
#print axioms ZFSet.isIso_curry
-- Canonical constructions and their universal properties
#print axioms ZFSet.ZFNat.Nat_eq_of_inductive
#print axioms ZFSet.funs_nat_recursion
#print axioms ZFSet.Sum.funs_coprod_universal
-- Finite cardinals: specification and uniqueness
#print axioms ZFSet.Card.spec
#print axioms ZFSet.Card.uniq
#print axioms ZFSet.ZFNat.eq_of_bijective
-- Set-level carriers of the quotient constructions and the transfers
#print axioms ZFSet.instEquivZFIntInt
#print axioms ZFSet.equivRatZFRat
#print axioms ZFSet.ZFNat.ringEquivNat
#print axioms ZFSet.ZFInt.equivInt
#print axioms ZFSet.ZFRat.equivRat
-- The case study (Sec. 6 of the paper)
#print axioms ZFSet.Imp.Expr.mem_dom_sem_iff
#print axioms ZFSet.Imp.Cmd.sem_pfunc
#print axioms ZFSet.Imp.Cmd.sem_seq_assoc
#print axioms ZFSet.Imp.Cmd.sem_whileDo_exit
#print axioms ZFSet.Imp.Cmd.sem_whileDo_step
#print axioms ZFSet.Imp.Cmd.sem_whileDo_unfold
#print axioms ZFSet.Imp.Cmd.not_mem_dom_assign_of_unassigned
#print axioms ZFSet.Imp.Cmd.assign_incr
#print axioms ZFSet.loop_pfunc
#print axioms ZFSet.loop_unfold

/-! ## Part 2 — exhaustive audit of every declaration of `ZFLean` and `Imp` -/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let names : List Name := env.constants.fold (fun l n _ => List.cons n l) List.nil
  let mut audited : Nat := 0
  let mut failures : Nat := 0
  for name in names do
    if name.isInternal then continue
    let some midx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[midx.toNat]!
    unless (`ZFLean).isPrefixOf mod || mod == `Imp do continue
    let axs ← collectAxioms name
    audited := audited + 1
    let offending := axs.filter (fun a => !allowed.contains a)
    unless offending.isEmpty do
      failures := failures + 1
      logError m!"{name} depends on {offending.toList}"
  logInfo m!"exhaustive audit: {audited} declarations from ZFLean and Imp; {failures} depend on an axiom outside propext, Classical.choice, Quot.sound"
  if failures != 0 then throwError "non-standard axioms found"
