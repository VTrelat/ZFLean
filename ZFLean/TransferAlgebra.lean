/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

-- re-exported: this file is the entry point for making `transfer` work on an
-- algebraic type, so importing it must bring `TransferEquiv`, `transfer_simps`
-- and the tactic itself along.
public import ZFLean.Transfer
public import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Order.Hom.Basic

/-!
# Transferring along bundled isomorphisms

When the equivalence a type is transferred along is the one underlying a bundled isomorphism
(`≃*`, `≃+`, `≃+*`, `≃o`, …), the lemmas saying how the operations are read in the target type
are already in Mathlib: they are `map_add`, `map_mul`, `map_ofNat` and others. This file puts
them in the `transfer_simps` simp set, so that such a type needs no lemma of its own for the
operations. The projection `f.toEquiv` and the coercion `↑f` are both normalized, so registering
```
noncomputable instance : TransferEquiv ZFInt ℤ := ⟨myRingEquiv.toEquiv⟩
```
is enough for `transfer ZFInt → ℤ => …` to deal with `+`, `*`, `-`, `0`, `1`, numerals, and the
casts.

Relations are not covered: no `map_…` lemma speaks about `≤` or `<`, and `OrderIso.le_iff_le`
cannot be turned around into a simp lemma as it stands, since the isomorphism it mentions is not
determined by its left-hand side. One line per relation and per type does it. State such a lemma
in the direction it is used, `a ≤ b ↔ myIso a ≤ myIso b`, rather than the other way round with a
`@[transfer_simps ←]` tag: both work, but the first reads as what it does.

## Making `transfer` work for a new type

1. Build the equivalence and bundle it: `≃+*` for a ring, `≃*` or `≃+` for a monoid or a group,
   `≃o` if the type is only ordered. This is where the mathematics is; the rest is bookkeeping.
2. Register it, with the projection `.toEquiv` or the coercion `↑`, both are recognized:
   `noncomputable instance : TransferEquiv ZFInt ℤ := ⟨myIso.toEquiv⟩`.
3. State what no `map_…` lemma covers, one line each:
   * the relations, stated in the direction they push:
     `@[transfer_simps] theorem le (a b : ZFInt) : a ≤ b ↔ myIso a ≤ myIso b := …`
   * divisibility, which `map_dvd_iff` states the wrong way round:
     `@[transfer_simps] theorem dvd (a b : ZFInt) : a ∣ b ↔ myIso a ∣ myIso b := …`
   * the operations that are outside the algebraic structure, such as `ZFNat.succ` or the
     division of `ℕ`: `@[transfer_simps] theorem succ (a) : myIso a.succ = (myIso a).succ := …`
   A lemma about numerals needs `no_index (OfNat.ofNat k)` on its left-hand side, otherwise its
   numeral is indexed as a literal and the lemma never fires.
4. Nothing else. `+ * - / ⁻¹ ^ 0 1`, numerals, the `ℕ` and `ℤ` casts, `= ∀ ∃`, and the binders of
   type `α`, `α → α`, `α × α` are dealt with by `transfer` itself.

The lemmas must be stated with the very equivalence that is registered: a lemma about `⇑e` does
not apply to a goal about `⇑myIso`, even when the two are definitionally equal. `ZFNat` is the
worked example, at the end of `ZFLean/NaturalsTransfered.lean`.
-/

attribute [transfer_simps]
  map_add map_mul map_zero map_one map_pow map_sub map_neg map_inv₀ map_div₀
  map_natCast map_intCast map_ratCast map_ofNat Nat.cast_id Int.cast_id Rat.cast_id
  MulEquiv.toEquiv_eq_coe MulEquiv.coe_toEquiv MulEquiv.coe_toEquiv_symm
  AddEquiv.toEquiv_eq_coe AddEquiv.coe_toEquiv AddEquiv.coe_toEquiv_symm
  RingEquiv.toEquiv_eq_coe RingEquiv.coe_toEquiv RingEquiv.coe_coe_toEquiv_symm
  OrderIso.coe_toEquiv
  MulEquiv.symm_symm AddEquiv.symm_symm RingEquiv.symm_symm OrderIso.symm_symm
  MulEquiv.apply_symm_apply MulEquiv.symm_apply_apply
  AddEquiv.apply_symm_apply AddEquiv.symm_apply_apply
  RingEquiv.apply_symm_apply RingEquiv.symm_apply_apply
  OrderIso.apply_symm_apply OrderIso.symm_apply_apply
