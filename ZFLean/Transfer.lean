/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Function.Iterate
public meta import Lean.Elab.Tactic

/-!
# The `transfer` tactic

`transfer α → β => tacs` turns a goal about `α` into the equivalent goal about `β` along an
equivalence `e : α ≃ β`, then runs `tacs` on it. The goal is rewritten in place, so closing
the transferred goal closes the original one: nothing has to be transferred back explicitly.

For instance, given `instance : TransferEquiv ZFNat ℕ := ⟨ringEquivNat.toEquiv⟩`,

```
example (n m : ZFNat) : n + m = m + n := by
  transfer ZFNat → ℕ =>
    rw [Nat.add_comm]
```

The equivalence is found by instance synthesis on `TransferEquiv α β`. It may also be given
explicitly, either as `transfer α → β using e => tacs`, or by naming it in place of the two
types, as `transfer e => tacs`, in which case the direction is read off the type of `e`. A
bundled isomorphism (`≃+*`, `≃*`, `≃o`, anything with an `EquivLike` instance) is accepted
wherever an equivalence is, and coerced to the equivalence underlying it. Going
the other way, as in `transfer e.symm => tacs`, only makes sense if `transfer_simps` holds the
lemmas for that direction: a simp set oriented the wrong way loops.

Transferring proceeds in three steps:

* every hypothesis whose type mentions `α` is reverted, and each binder `∀ (x : t), _` of the
  resulting goal whose type `t` is built out of `α` is replaced by `∀ (y : t[β/α]), _` through
  `Equiv.forall_congr_left`, which puts `E.symm y` where `x` used to be. The equivalence
  `E : t ≃ t[β/α]` is built from `e` by congruence, so that a function `f : α → α` is
  transferred to a function `β → β`, and so on for the type formers `congrEquiv` knows about;
* the `transfer_simps` simp set, together with `ne_eq` and lemmas lifting equalities and
  binders along the equivalences at hand, pushes them through the goal until no `α` is left.
  The lemmas of that simp set are what describes how the operations of `α` are read in `β`,
  e.g. `e (a + b) = e a + e b`;
* the reverted hypotheses are reintroduced under their original names, and `tacs` is run on the
  resulting goal.
-/

public section

universe u v

/-- Simp set used by the `transfer` tactic to push an equivalence through a goal. Its lemmas
state how the operations of the source type are read in the target type, e.g.
`e (a + b) = e a + e b` for the equivalence `e` a goal is transferred along. -/
register_simp_attr transfer_simps

/-- `TransferEquiv α β` bundles an equivalence `α ≃ β` as a class, so that `transfer α → β` can
find it by instance synthesis. -/
class TransferEquiv (α : Sort u) (β : Sort v) where
  /-- The equivalence along which goals are transferred. -/
  equiv : α ≃ β

namespace ZFLean.Transfer

open Lean Meta Elab Tactic

/-! ### Lemmas used to push equivalences through a goal

These are an implementation detail of the tactic, but they have to be public: the tactic looks
them up by name in the environment of the file it runs in, and a private declaration is not
exported to importing modules at all.
-/

/-- Applying `Equiv.arrowCongr` is conjugating. -/
theorem arrowCongr_apply {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
    (f : α₁ → β₁) (x : α₂) : e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) := rfl

/-- Applying the inverse of `Equiv.arrowCongr` is conjugating the other way round. This is
`Equiv.arrowCongr_symm` followed by `arrowCongr_apply`, but as a single step: rewriting with
`Equiv.arrowCongr_symm` alone would break the `E (E.symm x)` pattern that collapses an
equation between functions. -/
theorem arrowCongr_symm_apply {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
    (f : α₂ → β₂) (x : α₁) : (e₁.arrowCongr e₂).symm f x = e₂.symm (f (e₁ x)) := rfl

/-- Iterating a conjugated function is conjugating the iterate: this is what makes a statement
about `f^[n]` travel, `f` being a binder of type `α → α`. -/
theorem arrowCongr_symm_iterate {α β : Sort*} (e : α ≃ β) (f : β → β) (n : ℕ) (x : α) :
    ((e.arrowCongr e).symm f)^[n] x = e.symm (f^[n] (e x)) := by
  induction n generalizing x with
  | zero => exact (e.symm_apply_apply x).symm
  | succ n ih =>
    change ((e.arrowCongr e).symm f)^[n] (((e.arrowCongr e).symm f) x) = _
    rw [ih, arrowCongr_symm_apply, Equiv.apply_symm_apply]
    rfl

/-- Applying `Equiv.prodCongr` is applying both components. -/
theorem prodCongr_apply {α₁ α₂ β₁ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
    (p : α₁ × β₁) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) := rfl

/-- Applying the inverse of `Equiv.prodCongr` is applying both inverses. -/
theorem prodCongr_symm_apply {α₁ α₂ β₁ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
    (p : α₂ × β₂) : (e₁.prodCongr e₂).symm p = (e₁.symm p.1, e₂.symm p.2) := rfl

/-- `Equiv.forall_congr_left`, with `p` explicit so that it can be used as a simp lemma. -/
theorem forallLift {α : Sort u} {β : Sort v} (e : α ≃ β) (p : α → Prop) :
    (∀ x, p x) ↔ ∀ x, p (e.symm x) := e.forall_congr_left

/-- `Equiv.exists_congr_left`, with `p` explicit so that it can be used as a simp lemma. -/
theorem existsLift {α : Sort u} {β : Sort v} (e : α ≃ β) (p : α → Prop) :
    (∃ x, p x) ↔ ∃ x, p (e.symm x) := e.exists_congr_left

/-- An equation in `α` is the equation between the images in `β`. -/
theorem eqLift {α : Sort u} {β : Sort v} (e : α ≃ β) (x y : α) :
    x = y ↔ e x = e y := (e.apply_eq_iff_eq).symm

/-! ### Transporting the types of the binders -/

/-- The source and target types of an equivalence. -/
private meta def equivTypes (e : Expr) : MetaM (Expr × Expr) := do
  let t ← whnf (← inferType e)
  let some (α, β) := t.app2? ``Equiv
    | throwError "transfer: expected an equivalence, but{indentExpr e}\nhas type{indentExpr t}"
  return (α, β)

/-- Read a term as an equivalence: a `TransferEquiv` instance is unfolded, so that the
equivalence appears under the name the lemmas of `transfer_simps` are stated with, and a bundled
isomorphism (`≃+*`, `≃*`, `≃o`, …) is coerced to the equivalence underlying it. -/
private meta def asEquiv (e : Expr) : MetaM Expr := do
  let e ← withReducibleAndInstances (whnf e)
  let t ← whnf (← inferType e)
  if (t.app2? ``Equiv).isSome then return e
  try mkAppM ``EquivLike.toEquiv #[e]
  catch _ =>
    throwError "transfer: expected an equivalence, but{indentExpr e}\nhas type{indentExpr t}"

/-- A copy of the equivalence with fresh universe metavariables, together with its source type.
A universe polymorphic type may well occur at several universes in a single goal, each of them
calling for its own copy. -/
private meta def freshEquiv (eAbs : AbstractMVarsResult) : MetaM (Expr × Expr) := do
  let (_, _, E) ← openAbstractMVarsResult eAbs
  return (E, (← equivTypes E).1)

/-- Reads `t` as the source type of the equivalence, and returns the copy of the equivalence it
is the source of. -/
private meta def matchSource? (eAbs : AbstractMVarsResult) (t : Expr) : MetaM (Option Expr) := do
  let (E, α) ← freshEquiv eAbs
  -- The heads are compared after unfolding the reducible definitions, so that an abbreviation
  -- such as `ZFNat` and its unfolding `↥Nat` are recognised as the same type. A subterm under a
  -- binder still carries its loose bound variables, which `whnf` would choke on.
  let head (x : Expr) : MetaM Expr := do
    if x.hasLooseBVars then return x.getAppFn else return (← whnfR x).getAppFn
  match ← head α, ← head t with
  | .const a _, .const b _ => if a != b then return none
  | .fvar a, .fvar b => if a != b then return none
  | _, _ => return none
  if ← withReducible <| isDefEq t α then return some E else return none

/-- Does `t` mention the source type of the equivalence? -/
private meta partial def mentionsSource (eAbs : AbstractMVarsResult) (t : Expr) : MetaM Bool := do
  if (← matchSource? eAbs t).isSome then return true
  match t with
  | .app f a => mentionsSource eAbs f <||> mentionsSource eAbs a
  | .lam _ d b _ | .forallE _ d b _ => mentionsSource eAbs d <||> mentionsSource eAbs b
  | .letE _ d v b _ =>
    mentionsSource eAbs d <||> mentionsSource eAbs v <||> mentionsSource eAbs b
  | .mdata _ b | .proj _ _ b => mentionsSource eAbs b
  | _ => return false

/-- The equivalences built so far, each of them together with its source type. -/
private meta abbrev CongrM := StateRefT (Array (Expr × Expr)) MetaM

/-- Record an equivalence, unless one with the same source type is already known. -/
private meta def remember (t E : Expr) : CongrM Unit :=
  modify fun congrs => if congrs.any (·.1 == t) then congrs else congrs.push (t, E)

/-- The equivalence `t ≃ t[β/α]` transporting a type `t` built out of `α` to the same type built
out of `β`, or `none` when `t` is built by anything else than arrows and products. -/
private meta partial def congrEquiv (eAbs : AbstractMVarsResult) (t : Expr) :
    CongrM (Option Expr) := do
  if let some E ← matchSource? eAbs t then
    remember t E
    return some E
  unless ← mentionsSource eAbs t do return some (← mkAppM ``Equiv.refl #[t])
  let binary (n : Name) (t₁ t₂ : Expr) : CongrM (Option Expr) := do
    let some E₁ ← congrEquiv eAbs t₁ | return none
    let some E₂ ← congrEquiv eAbs t₂ | return none
    let E ← mkAppM n #[E₁, E₂]
    remember t E
    return some E
  match t with
  | .forallE _ d b _ => if b.hasLooseBVars then return none else binary ``Equiv.arrowCongr d b
  | _ => match t.app2? ``Prod with
    | some (t₁, t₂) => binary ``Equiv.prodCongr t₁ t₂
    | none => return none

/-- Record an equivalence for every occurrence of the source type inside `t`. A universe
polymorphic type may occur at several universes in one goal, and each of them needs its own
lifting lemmas. -/
private meta partial def collectSources (eAbs : AbstractMVarsResult) (t : Expr) : CongrM Unit := do
  if let some E ← matchSource? eAbs t then remember t E
  match t with
  | .app f a => collectSources eAbs f; collectSources eAbs a
  | .lam _ d b _ | .forallE _ d b _ =>
    -- The domain of a binder is a type: whatever `congrEquiv` can transport there is worth
    -- recording, so that a quantifier over, say, `α → α` gets its lifting lemmas too.
    if ← mentionsSource eAbs d then discard <| congrEquiv eAbs d
    collectSources eAbs d
    collectSources eAbs b
  | .letE _ d v b _ =>
    collectSources eAbs d; collectSources eAbs v; collectSources eAbs b
  | .mdata _ b | .proj _ _ b => collectSources eAbs b
  | _ => pure ()

/-! ### The tactic itself -/

/-- The lemmas lifting the equations and the binders of type `t` along `E : t ≃ t'`. They are of
no use, and would loop, when `t` and `t'` are the same type. -/
private meta def liftings (t E : Expr) : MetaM (Array Expr) := do
  let (α, β) ← equivTypes E
  if ← withNewMCtxDepth (isDefEq α β) then return #[]
  let lift (n : Name) (x : Expr) : MetaM Expr := do
    mkLambdaFVars #[x] (← mkAppM n #[E, x])
  let eq ← withLocalDeclD `x t fun x => withLocalDeclD `y t fun y => do
    mkLambdaFVars #[x, y] (← mkAppM ``eqLift #[E, x, y])
  withLocalDeclD `p (← mkArrow t (.sort .zero)) fun p => do
    return #[eq, ← lift ``forallLift p, ← lift ``existsLift p]

/-- The simp set pushing the equivalences of `congrs` through a goal. -/
private meta def transferTheorems (congrs : Array (Expr × Expr)) : MetaM SimpTheorems := do
  let some ext ← getSimpExtension? `transfer_simps
    | throwError "transfer: the `transfer_simps` simp set is not available"
  let mut thms ← ext.getTheorems
  for thm in [``ne_eq, ``Equiv.apply_symm_apply, ``Equiv.symm_apply_apply, ``Equiv.symm_symm,
      ``Equiv.trans_apply, ``Equiv.symm_trans_apply,
      ``Equiv.refl_apply, ``Equiv.refl_symm,
      ``arrowCongr_apply, ``arrowCongr_symm_apply, ``arrowCongr_symm_iterate,
      ``prodCongr_apply, ``prodCongr_symm_apply] do
    thms ← thms.addConst thm
  for (t, E) in congrs do
    for lift in ← liftings t E do
      thms ← thms.add (.other `transfer.lift) #[] lift
  return thms

/-- Replace the leading binder `∀ (x : α), p x` of `g` by `∀ (y : β), p (E.symm y)`, where
`E : α ≃ β`. -/
private meta def transferBinder (g : MVarId) (E : Expr) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let .forallE n d body bi := tgt
    | throwError "transfer: expected a `∀` goal, but got{indentExpr tgt}"
  unless ← isProp tgt do
    throwError "transfer: cannot transfer the binder `{n}`, the goal{indentExpr tgt}\n\
      is not a proposition"
  let iff ← mkAppOptM ``Equiv.forall_congr_left #[none, none, some (.lam n d body bi), some E]
  let some (_, rhs) := (← instantiateMVars (← inferType iff)).iff?
    | throwError "transfer: `Equiv.forall_congr_left` is not an iff"
  let .forallE _ d' body' bi' := rhs
    | throwError "transfer: `Equiv.forall_congr_left` is not a `∀`"
  let g' ← mkFreshExprSyntheticOpaqueMVar (.forallE n d' body'.headBeta bi') (← g.getTag)
  g.assign (← mkAppM ``Iff.mpr #[iff, g'])
  return g'.mvarId!

/-- Transfer the main goal along `e`, then run `tacs` on the transferred goal. -/
private meta def transferGoal (e : Expr) (tacs : TSyntax ``Parser.Tactic.tacticSeq) :
    TacticM Unit := do
  let e ← asEquiv e
  let (α, _) ← equivTypes e
  let eAbs ← abstractMVars e
  let g :: rest ← getGoals | throwError "transfer: no goals to be proved"
  -- Everything mentioning `α` goes back into the goal, so that its binders can be transferred.
  let (names, g) ← g.withContext do
    let mut toRevert := #[]
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        if ← mentionsSource eAbs decl.type then toRevert := toRevert.push decl.fvarId
    let (reverted, g) ← g.revert toRevert
    return (← reverted.mapM (·.getUserName), g)
  -- Each binder built out of `α` is transferred; the others are left alone. Binders of the goal
  -- itself are transferred as well, as long as they are in front of it.
  let mut g := g
  let mut fvars := #[]
  let mut own := #[]
  let mut congrs := #[(α, e)]
  let mut i := 0
  repeat
    let some (bn, d) ← g.withContext do
        match ← instantiateMVars (← g.getType) with
        | .forallE bn d _ _ => return some (bn, d)
        | _ => return none
      | break
    let (E?, congrs') ← g.withContext do
      if ← mentionsSource eAbs d then (congrEquiv eAbs d).run congrs else return (none, congrs)
    congrs := congrs'
    let reverted := i < names.size
    unless reverted || E?.isSome do break
    if let some E := E? then g ← transferBinder g E
    let (fvar, g') ← g.intro (if h : i < names.size then names[i] else bn)
    g := g'
    if reverted then fvars := fvars.push fvar else own := own.push fvar
    i := i + 1
  -- The binders of the goal are put back where they were.
  unless own.isEmpty do
    let (_, g') ← g.revert own
    g := g'
  -- The source type may still occur, at other universes, in places that are not binders.
  congrs ← g.withContext do
    let mut acc := congrs
    for t in (← fvars.mapM fun fvar => do return (← fvar.getDecl).type).push (← g.getType) do
      acc := (← (collectSources eAbs (← instantiateMVars t)).run acc).2
    return acc
  -- A universe that the goal does not pin down is arbitrary — that happens when transferring
  -- *to* a polymorphic type, as in `transfer ℕ → ZFNat`. Left as a metavariable it would stop
  -- simp from matching anything at all, so fix it now that the goal has had its say.
  g.withContext do
    let mut st := collectLevelMVars {} (← instantiateMVars (← g.getType))
    for fvar in fvars do
      st := collectLevelMVars st (← instantiateMVars (← fvar.getType))
    for (t, E) in congrs do
      st := collectLevelMVars (collectLevelMVars st (← instantiateMVars t)) (← instantiateMVars E)
    for u in st.result do
      assignLevelMVar u Level.zero
  -- Push the equivalences through the goal and the reintroduced hypotheses.
  -- `failIfUnchanged := false`: a goal that is already free of `α` is left alone rather than
  -- making the tactic fail.
  let ctx ← Simp.mkContext (config := { failIfUnchanged := false })
    (simpTheorems := #[← transferTheorems congrs]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx (fvarIdsToSimp := fvars)
  let some (_, transferred) := r
    | logWarning "transfer: the goal was closed by the transfer itself, the block is unused"
      setGoals rest
      return
  setGoals [transferred]
  evalTactic tacs
  setGoals ((← getGoals) ++ rest)

/--
`transfer α → β => tacs` transfers the goal along an equivalence `α ≃ β` and runs `tacs` on the
transferred goal, which now talks about `β` instead of `α`:

```
example (n m : ZFNat) : n + m = m + n := by
  transfer ZFNat → ℕ =>
    rw [Nat.add_comm]
```

The equivalence is synthesized from a `TransferEquiv α β` instance, or given explicitly by
`transfer α → β using e => tacs`. Passing the equivalence alone, as in `transfer e => tacs`, is
also accepted: the direction is then read off the type of `e`. In both cases `e` may be a
bundled isomorphism, such as a `≃+*` or a `≃o`.
-/
syntax (name := transfer) "transfer " term (" using " term)? " => " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| transfer $t:term $[using $e?]? => $tacs) => withMainContext do
    let e ← match t with
      | `($α:term → $β:term) => do
        let α ← Term.elabType α
        let β ← Term.elabType β
        match e? with
        | some e =>
          let e ← asEquiv (← Term.elabTerm e none)
          let (α', β') ← equivTypes e
          unless (← isDefEq α α') && (← isDefEq β β') do
            throwError "transfer: the equivalence{indentExpr e}\ndoes not go from\
              {indentExpr α}\nto{indentExpr β}"
          pure e
        | none =>
          let cls ← mkAppM ``TransferEquiv #[α, β]
          let inst ←
            try synthInstance cls
            catch _ =>
              throwError "transfer: no instance{indentExpr cls}\n\
                was found; pass the equivalence explicitly with `using`"
          mkAppOptM ``TransferEquiv.equiv #[α, β, inst]
      | _ =>
        if e?.isSome then
          throwError "transfer: `using` expects the source and target types, as in \
            `transfer α → β using e`"
        Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    transferGoal (← instantiateMVars e) tacs

end ZFLean.Transfer

end
