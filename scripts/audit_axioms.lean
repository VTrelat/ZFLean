/-
Axiom audit of the headline results of ZFLean.

Run with `lake env lean scripts/audit_axioms.lean` (after `lake build`, which also builds the
case study `casestudy/Imp.lean`, target `Imp`). Every line must list
at most `propext`, `Classical.choice` and `Quot.sound`; `scripts/check.sh` fails if `sorryAx`
appears.
-/
import ZFLean
import Imp

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
-- Set-level carriers of the quotient constructions and the transfers
#print axioms ZFSet.instEquivZFIntInt
#print axioms ZFSet.equivRatZFRat
#print axioms ZFSet.ZFNat.ringEquivNat
#print axioms ZFSet.ZFInt.equivInt
#print axioms ZFSet.ZFRat.equivRat
