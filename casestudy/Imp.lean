/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import ZFLean

/-!
# Case study: a denotational semantics on set-level stores

A small imperative language — literals, variables and addition; `skip`, assignment,
sequencing and a conditional — receives a denotational semantics inside the model. Stores are
the *set* `Store V` of partial functions from the set `V` of variable names to `Nat`; an
expression denotes a partial function `Store V ⇸ Nat`, defined exactly on the stores that
assign all its variables (`Expr.mem_dom_sem_iff`); a command denotes a relation on `Store V`,
which is a partial function (`Cmd.sem_pfunc`: the language is deterministic). Program
equivalence is equality of denotations, i.e. equality of sets (`Cmd.sem_seq_assoc`, …).

The file is a *client* of the library: a separate Lake target (`Imp`, see `lakefile.toml`)
that imports `ZFLean` as any downstream project would. Its first section adds the two operations
of the relational calculus that the semantics needs — domain restriction `S ◁ R` and override
`σ[x ↦ n]` — with their closure lemmas tagged for `zrel`/`zpfun`/`zdom`; the semantics itself
then uses the library as is.
-/

public noncomputable section

namespace ZFSet

/-! ## Domain restriction, override, unions of partial functions -/

/-- `S ◁ R`: the pairs of `R` whose first component lies in `S` (B's domain restriction). -/
@[irreducible] def domRestrict (S R : ZFSet) : ZFSet := R.sep fun p => ∃ x y, p = x.pair y ∧ x ∈ S
infixr:70 " ◁ " => domRestrict

theorem mem_domRestrict {S R x y : ZFSet} : x.pair y ∈ S ◁ R ↔ x ∈ S ∧ x.pair y ∈ R := by
  rw [domRestrict, mem_sep]
  constructor
  · rintro ⟨hR, x', y', hp, hx⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.mp hp
    exact ⟨hx, hR⟩
  · rintro ⟨hx, hR⟩
    exact ⟨hR, x, y, rfl, hx⟩

theorem domRestrict_subset {S R : ZFSet} : S ◁ R ⊆ R := by
  rw [domRestrict]; exact sep_subset

@[zrel] theorem domRestrict_is_rel {S R A B : ZFSet} (hR : R ⊆ A.prod B) : S ◁ R ⊆ A.prod B :=
  fun _ hp => hR (domRestrict_subset hp)

@[zpfun] theorem IsPFunc.domRestrict {S R A B : ZFSet} (hR : R.IsPFunc A B) :
    (S ◁ R).IsPFunc A B :=
  ⟨domRestrict_is_rel hR.1,
    fun x y hxy z hxz => hR.2 x y (domRestrict_subset hxy) z (domRestrict_subset hxz)⟩

/-- `σ[x ↦ n]`: `σ` with `x` (re)assigned to `n` (B's override `σ <+ {x ↦ n}`). -/
@[irreducible] def override (σ x n : ZFSet) : ZFSet :=
  (σ.sep fun p => ∃ y m, p = y.pair m ∧ y ≠ x) ∪ {x.pair n}
notation:max σ "[" x " ↦ " n "]" => override σ x n

theorem mem_override {σ x n y m : ZFSet} :
    y.pair m ∈ σ[x ↦ n] ↔ (y ≠ x ∧ y.pair m ∈ σ) ∨ (y = x ∧ m = n) := by
  rw [override, mem_union, mem_sep, mem_singleton, pair_inj]
  constructor
  · rintro (⟨hσ, y', m', hp, hy⟩ | ⟨rfl, rfl⟩)
    · obtain ⟨rfl, rfl⟩ := pair_inj.mp hp
      exact Or.inl ⟨hy, hσ⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨hy, hσ⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨hσ, y, m, rfl, hy⟩
    · exact Or.inr ⟨rfl, rfl⟩

theorem pair_mem_override_self {σ x n : ZFSet} : x.pair n ∈ σ[x ↦ n] :=
  mem_override.mpr (Or.inr ⟨rfl, rfl⟩)

@[zrel] theorem override_is_rel {σ x n A B : ZFSet} (hσ : σ ⊆ A.prod B) (hx : x ∈ A)
    (hn : n ∈ B) : σ[x ↦ n] ⊆ A.prod B := by
  intro p hp
  rw [override, mem_union, mem_sep, mem_singleton] at hp
  rcases hp with ⟨hσp, -⟩ | rfl
  · exact hσ hσp
  · exact pair_mem_prod.mpr ⟨hx, hn⟩

@[zpfun] theorem IsPFunc.override {σ x n A B : ZFSet} (hσ : σ.IsPFunc A B) (hx : x ∈ A)
    (hn : n ∈ B) : (σ[x ↦ n]).IsPFunc A B := by
  refine ⟨override_is_rel hσ.1 hx hn, fun y m hym m' hym' => ?_⟩
  rw [mem_override] at hym hym'
  rcases hym with ⟨hy, hσm⟩ | ⟨rfl, rfl⟩
  · rcases hym' with ⟨-, hσm'⟩ | ⟨rfl, -⟩
    · exact hσ.2 y m hσm m' hσm'
    · exact absurd rfl hy
  · rcases hym' with ⟨hy', -⟩ | ⟨-, rfl⟩
    · exact absurd rfl hy'
    · rfl

/-- `x` is in the domain of `σ[x ↦ n]`: the well-definedness rule of an override. Its
hypotheses have the shape of `mem_dom_of_mem`, so that `zdom` closes them from the context. -/
@[zdom] theorem mem_dom_override_self {σ x n A B : ZFSet} (hσ : σ.IsPFunc A B) (hx : x ∈ A)
    (hn : n ∈ B) : x ∈ (σ[x ↦ n]).Dom (is_rel_of_is_pfunc (IsPFunc.override hσ hx hn)) :=
  mem_dom_of (override_is_rel hσ.1 hx hn) pair_mem_override_self

theorem mem_dom_override {σ x n A B y : ZFSet} (hσ : σ ⊆ A.prod B) (hx : x ∈ A) (hn : n ∈ B) :
    y ∈ (σ[x ↦ n]).Dom (override_is_rel hσ hx hn) ↔ y = x ∨ y ∈ σ.Dom hσ := by
  rw [mem_dom_iff (override_is_rel hσ hx hn), mem_dom_iff hσ]
  constructor
  · rintro ⟨m, hm⟩
    rcases mem_override.mp hm with ⟨-, hσm⟩ | ⟨rfl, -⟩
    · exact Or.inr ⟨m, hσm⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨m, hm⟩)
    · exact ⟨n, pair_mem_override_self⟩
    · by_cases hy : y = x
      · exact ⟨n, mem_override.mpr (Or.inr ⟨hy, rfl⟩)⟩
      · exact ⟨m, mem_override.mpr (Or.inl ⟨hy, hm⟩)⟩

/-- Reading back the overridden variable. -/
theorem fapply_override_self {σ x n A B : ZFSet} (hσ : σ.IsPFunc A B) (hx : x ∈ A) (hn : n ∈ B) :
    @ᶻ(σ[x ↦ n]) ⟨x, by zdom⟩ = ⟨n, hn⟩ :=
  fapply.of_pair (IsPFunc.override hσ hx hn) pair_mem_override_self

@[zrel] theorem union_is_rel {f g A B : ZFSet} (hf : f ⊆ A.prod B) (hg : g ⊆ A.prod B) :
    f ∪ g ⊆ A.prod B := by
  intro p hp
  rcases mem_union.mp hp with hp | hp
  · exact hf hp
  · exact hg hp

/-- Two partial functions with disjoint domains have a partial function as union. -/
@[zpfun] theorem IsPFunc.union {f g A B : ZFSet} (hf : f.IsPFunc A B) (hg : g.IsPFunc A B)
    (h : ∀ x y z : ZFSet, x.pair y ∈ f → x.pair z ∈ g → False) : (f ∪ g).IsPFunc A B := by
  refine ⟨union_is_rel hf.1 hg.1, fun x y hxy z hxz => ?_⟩
  rcases mem_union.mp hxy with hxy | hxy <;> rcases mem_union.mp hxz with hxz | hxz
  · exact hf.2 x y hxy z hxz
  · exact (h x y z hxy hxz).elim
  · exact (h x z y hxz hxy).elim
  · exact hg.2 x y hxy z hxz

/-- An abstraction is a partial function whatever its body does; it is total when the body
stays in the range (`lambda_isFunc`). -/
@[zpfun] theorem lambda_isPFunc {A B : ZFSet} {f : ZFSet → ZFSet} : (lambda A B f).IsPFunc A B := by
  refine ⟨lambda_subset, fun x y hxy z hxz => ?_⟩
  rw [lambda_spec] at hxy hxz
  rw [hxy.2.2, hxz.2.2]

/-! ## Stores -/

namespace Imp

/-- The state space: the set of partial functions from the variable names `V` to `Nat`. -/
@[irreducible] def Store (V : ZFSet) : ZFSet := (V.prod Nat).powerset.sep fun σ => σ.IsPFunc V Nat

variable {V : ZFSet}

theorem mem_Store {σ : ZFSet} : σ ∈ Store V ↔ σ.IsPFunc V Nat := by
  rw [Store, mem_sep, mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

@[zpfun] theorem IsPFunc_of_mem_Store {σ : ZFSet} (hσ : σ ∈ Store V) : σ.IsPFunc V Nat :=
  mem_Store.mp hσ

theorem override_mem_Store {σ x n : ZFSet} (hσ : σ ∈ Store V) (hx : x ∈ V) (hn : n ∈ Nat) :
    σ[x ↦ n] ∈ Store V :=
  mem_Store.mpr (IsPFunc.override (IsPFunc_of_mem_Store hσ) hx hn)

/-! ## Expressions -/

/-- Expressions over the variable names `V`. -/
inductive Expr (V : ZFSet)
  | lit : ZFNat → Expr V
  | var : V → Expr V
  | add : Expr V → Expr V → Expr V

namespace Expr

/-- The denotation of an expression: a set of pairs `(σ, n)` with `σ ∈ Store V` and `n ∈ Nat`,
which is a partial function `Store V ⇸ Nat` (`Expr.sem_pfunc`). -/
def sem : Expr V → ZFSet
  | lit n => λᶻ : Store V → Nat | _σ ↦ n.val
  | var x => ((Store V).prod Nat).sep fun p => ∃ σ n : ZFSet, p = σ.pair n ∧ x.val.pair n ∈ σ
  | add e₁ e₂ => ((Store V).prod Nat).sep fun p => ∃ σ : ZFSet, ∃ n₁ n₂ : ZFNat,
      p = σ.pair (n₁ + n₂).val ∧ σ.pair n₁.val ∈ e₁.sem ∧ σ.pair n₂.val ∈ e₂.sem

notation:max "⟦" e "⟧ₑ" => Expr.sem e

@[simp] theorem sem_lit (n : ZFNat) :
    ⟦(lit n : Expr V)⟧ₑ = λᶻ : Store V → Nat | _σ ↦ n.val := by
  rw [sem]
@[simp] theorem sem_var (x : V) :
    ⟦var x⟧ₑ =
      ((Store V).prod Nat).sep fun p => ∃ σ n : ZFSet, p = σ.pair n ∧ x.val.pair n ∈ σ := by
  rw [sem]
@[simp] theorem sem_add (e₁ e₂ : Expr V) :
    ⟦add e₁ e₂⟧ₑ = ((Store V).prod Nat).sep fun p => ∃ σ : ZFSet, ∃ n₁ n₂ : ZFNat,
      p = σ.pair (n₁ + n₂).val ∧ σ.pair n₁.val ∈ ⟦e₁⟧ₑ ∧ σ.pair n₂.val ∈ ⟦e₂⟧ₑ := by
  rw [sem]

/- Once its equations are available, the denotation is made opaque to unification: applied to
a constructor it would otherwise unfold to its body whenever a seed lemma is tried against it,
which is exactly the cost `with_reducible` keeps out of the searches. -/
attribute [irreducible] sem

@[zrel] theorem sem_is_rel (e : Expr V) : ⟦e⟧ₑ ⊆ (Store V).prod Nat := by
  cases e with
  | lit n => rw [sem_lit]; exact lambda_subset
  | var x => rw [sem_var]; exact sep_subset
  | add e₁ e₂ => rw [sem_add]; exact sep_subset

theorem mem_sem_lit {σ m : ZFSet} {n : ZFNat} :
    σ.pair m ∈ ⟦(lit n : Expr V)⟧ₑ ↔ σ ∈ Store V ∧ m = n.val := by
  rw [sem_lit, lambda_spec]
  constructor
  · rintro ⟨hσ, -, rfl⟩
    exact ⟨hσ, rfl⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨hσ, n.property, rfl⟩

theorem mem_sem_var {σ m : ZFSet} {x : V} :
    σ.pair m ∈ ⟦var x⟧ₑ ↔ σ ∈ Store V ∧ x.val.pair m ∈ σ := by
  rw [sem_var, mem_sep, pair_mem_prod]
  constructor
  · rintro ⟨⟨hσ, -⟩, σ', n', hp, hx⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.mp hp
    exact ⟨hσ, hx⟩
  · rintro ⟨hσ, hx⟩
    exact ⟨⟨hσ, (pair_mem_prod.mp ((IsPFunc_of_mem_Store hσ).1 hx)).2⟩, σ, m, rfl, hx⟩

theorem mem_sem_add {σ m : ZFSet} {e₁ e₂ : Expr V} :
    σ.pair m ∈ ⟦add e₁ e₂⟧ₑ ↔
      ∃ n₁ n₂ : ZFNat, m = (n₁ + n₂).val ∧ σ.pair n₁.val ∈ ⟦e₁⟧ₑ ∧ σ.pair n₂.val ∈ ⟦e₂⟧ₑ := by
  rw [sem_add, mem_sep]
  constructor
  · rintro ⟨-, σ', n₁, n₂, hp, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.mp hp
    exact ⟨n₁, n₂, rfl, h₁, h₂⟩
  · rintro ⟨n₁, n₂, rfl, h₁, h₂⟩
    exact ⟨pair_mem_prod.mpr ⟨(pair_mem_prod.mp (sem_is_rel e₁ h₁)).1, (n₁ + n₂).property⟩,
      σ, n₁, n₂, rfl, h₁, h₂⟩

/-- A literal is defined on every store. -/
@[zfun] theorem sem_lit_isFunc (n : ZFNat) : (Store V).IsFunc Nat ⟦(lit n : Expr V)⟧ₑ := by
  rw [sem_lit]; exact lambda_isFunc fun _ => n.property

/-- Expressions denote partial functions: evaluation is deterministic. -/
@[zpfun] theorem sem_pfunc (e : Expr V) : ⟦e⟧ₑ.IsPFunc (Store V) Nat := by
  refine ⟨sem_is_rel e, ?_⟩
  induction e with
  | lit n =>
    intro σ m hm m' hm'
    rw [(mem_sem_lit.mp hm).2, (mem_sem_lit.mp hm').2]
  | var x =>
    intro σ m hm m' hm'
    rw [mem_sem_var] at hm hm'
    exact (IsPFunc_of_mem_Store hm.1).2 _ _ hm.2 _ hm'.2
  | add e₁ e₂ ih₁ ih₂ =>
    intro σ m hm m' hm'
    obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := mem_sem_add.mp hm
    obtain ⟨n₁', n₂', rfl, h₁', h₂'⟩ := mem_sem_add.mp hm'
    rw [Subtype.ext (ih₁ _ _ h₁ _ h₁'), Subtype.ext (ih₂ _ _ h₂ _ h₂')]

/-- The set of variables occurring in an expression, a subset of `V`. -/
def FV : Expr V → ZFSet
  | lit _ => ∅
  | var x => {x.val}
  | add e₁ e₂ => FV e₁ ∪ FV e₂

/-- Definedness: `e` is defined at `σ` exactly when `σ` assigns every variable of `e` — the
well-definedness condition of B, here a theorem about domains. -/
theorem mem_dom_sem_iff {σ : ZFSet} (hσ : σ ∈ Store V) (e : Expr V) :
    σ ∈ ⟦e⟧ₑ.Dom ↔ e.FV ⊆ σ.Dom := by
  induction e with
  | lit n =>
    rw [FV, is_func_dom_eq (sem_lit_isFunc n)]
    exact ⟨fun _ => empty_subset _, fun _ => hσ⟩
  | var x =>
    rw [FV, mem_dom_iff (sem_is_rel _), singleton_subset_mem_iff,
      mem_dom_iff (is_rel_of_is_pfunc (IsPFunc_of_mem_Store hσ))]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, (mem_sem_var.mp hm).2⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, mem_sem_var.mpr ⟨hσ, hm⟩⟩
  | add e₁ e₂ ih₁ ih₂ =>
    rw [FV]
    constructor
    · intro h y hy
      obtain ⟨m, hm⟩ := (mem_dom_iff (sem_is_rel _)).mp h
      obtain ⟨n₁, n₂, -, h₁, h₂⟩ := mem_sem_add.mp hm
      rcases mem_union.mp hy with hy | hy
      · exact ih₁.mp ((mem_dom_iff (sem_is_rel _)).mpr ⟨_, h₁⟩) hy
      · exact ih₂.mp ((mem_dom_iff (sem_is_rel _)).mpr ⟨_, h₂⟩) hy
    · intro h
      obtain ⟨m₁, hm₁⟩ :=
        (mem_dom_iff (sem_is_rel _)).mp (ih₁.mpr fun y hy => h (mem_union.mpr (Or.inl hy)))
      obtain ⟨m₂, hm₂⟩ :=
        (mem_dom_iff (sem_is_rel _)).mp (ih₂.mpr fun y hy => h (mem_union.mpr (Or.inr hy)))
      have hn₁ : m₁ ∈ Nat := (pair_mem_prod.mp (sem_is_rel e₁ hm₁)).2
      have hn₂ : m₂ ∈ Nat := (pair_mem_prod.mp (sem_is_rel e₂ hm₂)).2
      exact (mem_dom_iff (sem_is_rel _)).mpr
        ⟨_, mem_sem_add.mpr ⟨⟨m₁, hn₁⟩, ⟨m₂, hn₂⟩, rfl, hm₁, hm₂⟩⟩

/-- The stores on which `e` is defined and nonzero. -/
@[irreducible] def tt (e : Expr V) : ZFSet := (Store V).sep fun σ => ∃ n, σ.pair n ∈ ⟦e⟧ₑ ∧ n ≠ ∅
/-- The stores on which `e` is defined and zero. -/
@[irreducible] def ff (e : Expr V) : ZFSet := (Store V).sep fun σ => σ.pair ∅ ∈ ⟦e⟧ₑ

theorem tt_ff_disjoint (e : Expr V) {σ : ZFSet} (ht : σ ∈ e.tt) (hf : σ ∈ e.ff) : False := by
  rw [tt, mem_sep] at ht
  rw [ff, mem_sep] at hf
  obtain ⟨-, n, hn, n_ne⟩ := ht
  exact n_ne ((sem_pfunc e).2 σ n hn ∅ hf.2)

end Expr

/-! ## Commands -/

/-- Commands over the variable names `V`. -/
inductive Cmd (V : ZFSet)
  | skip : Cmd V
  | assign : V → Expr V → Cmd V
  | seq : Cmd V → Cmd V → Cmd V
  | ite : Expr V → Cmd V → Cmd V → Cmd V

namespace Cmd
open Expr

/-- The denotation of a command: a relation on `Store V`, in fact a partial function
(`Cmd.sem_pfunc`). An assignment is defined exactly where its expression is; the domain
proof `h` is the abstraction's own binder. -/
def sem : Cmd V → ZFSet
  | skip => 𝟙(Store V)
  | assign x e => λᶻ : ⟦e⟧ₑ.Dom → Store V | h : σ ↦ σ[x.val ↦ (@ᶻ⟦e⟧ₑ ⟨σ, h⟩).val]
  | seq c₁ c₂ => composition c₂.sem c₁.sem (Store V) (Store V) (Store V)
  | ite e c₁ c₂ => (e.tt ◁ c₁.sem) ∪ (e.ff ◁ c₂.sem)

notation:max "⟦" c "⟧ᶜ" => Cmd.sem c

@[simp] theorem sem_skip : ⟦(skip : Cmd V)⟧ᶜ = 𝟙(Store V) := by rw [sem]
@[simp] theorem sem_assign (x : V) (e : Expr V) :
    ⟦assign x e⟧ᶜ = λᶻ : ⟦e⟧ₑ.Dom → Store V | h : σ ↦ σ[x.val ↦ (@ᶻ⟦e⟧ₑ ⟨σ, h⟩).val] := by
  rw [sem]
@[simp] theorem sem_seq (c₁ c₂ : Cmd V) :
    ⟦seq c₁ c₂⟧ᶜ = composition ⟦c₂⟧ᶜ ⟦c₁⟧ᶜ (Store V) (Store V) (Store V) := by rw [sem]
@[simp] theorem sem_ite (e : Expr V) (c₁ c₂ : Cmd V) :
    ⟦ite e c₁ c₂⟧ᶜ = (e.tt ◁ ⟦c₁⟧ᶜ) ∪ (e.ff ◁ ⟦c₂⟧ᶜ) := by rw [sem]

attribute [irreducible] sem

/-- Commands denote partial functions: the language is deterministic. Every case is closed by
`zpfun`; the conditional needs the disjointness of the two guards as a hypothesis. -/
@[zpfun] theorem sem_pfunc (c : Cmd V) : ⟦c⟧ᶜ.IsPFunc (Store V) (Store V) := by
  induction c with
  | skip => rw [sem_skip]; zpfun
  | assign x e =>
    rw [sem_assign]
    exact pfunc_weaken lambda_isPFunc (dom_subset _ _) fun _ h => h
  | seq c₁ c₂ ih₁ ih₂ => rw [sem_seq]; zpfun
  | ite e c₁ c₂ ih₁ ih₂ =>
    rw [sem_ite]
    have hd : ∀ σ τ τ' : ZFSet, σ.pair τ ∈ e.tt ◁ ⟦c₁⟧ᶜ → σ.pair τ' ∈ e.ff ◁ ⟦c₂⟧ᶜ → False :=
      fun σ τ τ' h₁ h₂ => tt_ff_disjoint e (mem_domRestrict.mp h₁).1 (mem_domRestrict.mp h₂).1
    apply IsPFunc.union <;> zpfun

@[zrel] theorem sem_is_rel (c : Cmd V) : ⟦c⟧ᶜ ⊆ (Store V).prod (Store V) := (sem_pfunc c).1

/-- An assignment is a total function from the stores where its expression is defined. Not a
`zfun` seed: on a goal `IsFunc ?A ?B ⟦assign x e⟧ᶜ` it would fix `?A` to `⟦e⟧ₑ.Dom`, and an
autoparam elaborated earlier cannot be revisited when a later one needs `?A = Store V`
(`sem_assign_lit_isFunc` below). -/
theorem sem_assign_isFunc (x : V) (e : Expr V) :
    ⟦e⟧ₑ.Dom.IsFunc (Store V) ⟦assign x e⟧ᶜ := by
  rw [sem_assign]
  apply lambda_isFunc
  intro σ hσ
  rw [dite_cond_eq_true (eq_true hσ)]
  exact override_mem_Store (dom_subset _ _ hσ) x.property (fapply_mem_range _ hσ)

/-- An assignment of a literal is defined on every store. -/
@[zfun] theorem sem_assign_lit_isFunc (x : V) (n : ZFNat) :
    (Store V).IsFunc (Store V) ⟦assign x (lit n)⟧ᶜ := by
  have h := sem_assign_isFunc x (lit n)
  rwa [is_func_dom_eq (sem_lit_isFunc n)] at h

/-- Sequencing preserves totality. -/
@[zfun] theorem sem_seq_isFunc {c₁ c₂ : Cmd V} (h₁ : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ)
    (h₂ : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ) : (Store V).IsFunc (Store V) ⟦seq c₁ c₂⟧ᶜ := by
  rw [sem_seq]; exact IsFunc_of_composition_IsFunc h₂ h₁

/-- On total commands, sequencing is the composition `∘ᶻ` of the relational calculus, whose
totality obligations `zfun` discharges from the two rules above. -/
theorem sem_seq_eq_fcomp {c₁ c₂ : Cmd V} (h₁ : (Store V).IsFunc (Store V) ⟦c₁⟧ᶜ)
    (h₂ : (Store V).IsFunc (Store V) ⟦c₂⟧ᶜ) : ⟦seq c₁ c₂⟧ᶜ = ⟦c₂⟧ᶜ ∘ᶻ ⟦c₁⟧ᶜ := sem_seq c₁ c₂

/-- Running `x := n; y := m` on a store: `fapply_composition` of the library, every
side condition — two totality facts, one partial-functionality fact, three domain
memberships — discharged by the tactics. -/
example (x y : V) (n m : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    @ᶻ(⟦assign y (lit m)⟧ᶜ ∘ᶻ ⟦assign x (lit n)⟧ᶜ) ⟨σ, by zdom⟩ =
      @ᶻ⟦assign y (lit m)⟧ᶜ ⟨(@ᶻ⟦assign x (lit n)⟧ᶜ ⟨σ, by zdom⟩).val, by zdom⟩ :=
  fapply_composition _ _ hσ

/-- Definedness of an assignment is definedness of its expression. -/
theorem mem_dom_sem_assign_iff {σ : ZFSet} (x : V) (e : Expr V) :
    σ ∈ ⟦assign x e⟧ᶜ.Dom ↔ σ ∈ ⟦e⟧ₑ.Dom := by
  rw [mem_dom_iff (sem_is_rel _), ← mem_dom_iff (is_rel_of_is_func (sem_assign_isFunc x e)),
    is_func_dom_eq (sem_assign_isFunc x e)]

/-! ### Program equivalence is equality of denotations -/

theorem sem_seq_skip (c : Cmd V) : ⟦seq c skip⟧ᶜ = ⟦c⟧ᶜ := by
  rw [sem_seq, sem_skip, Id.composition_left (sem_is_rel c)]

theorem sem_skip_seq (c : Cmd V) : ⟦seq skip c⟧ᶜ = ⟦c⟧ᶜ := by
  rw [sem_seq, sem_skip, Id.composition_right (sem_is_rel c)]

theorem sem_seq_assoc (c₁ c₂ c₃ : Cmd V) : ⟦seq (seq c₁ c₂) c₃⟧ᶜ = ⟦seq c₁ (seq c₂ c₃)⟧ᶜ := by
  rw [sem_seq, sem_seq, sem_seq, sem_seq, composition_assoc]

/-! ### Two facts about assignments -/

/-- `x := y + 1` is undefined on a store that does not assign `y`: the well-definedness
obligation of the assignment, read off the domains. -/
theorem not_mem_dom_assign_of_unassigned (x y : V) {σ : ZFSet} (hσ : σ ∈ Store V)
    (hy : y.val ∉ σ.Dom) : σ ∉ ⟦assign x (add (var y) (lit 1))⟧ᶜ.Dom := by
  rw [mem_dom_sem_assign_iff, mem_dom_sem_iff hσ]
  intro h
  exact hy (h (mem_union.mpr (Or.inl (mem_singleton.mpr rfl))))

/-- `x := x + 1` increases the value of `x`. The arithmetic step, `n < n + 1` on `ZFNat`, is
transferred to `ℕ` and closed by `omega`. -/
theorem assign_incr (x : V) {σ σ' : ZFSet} (h : σ.pair σ' ∈ ⟦assign x (add (var x) (lit 1))⟧ᶜ) :
    ∃ n m : ZFNat, x.val.pair n.val ∈ σ ∧ x.val.pair m.val ∈ σ' ∧ n < m := by
  rw [sem_assign, lambda_spec] at h
  obtain ⟨hσ, -, rfl⟩ := h
  rw [dif_pos hσ]
  obtain ⟨n₁, n₂, hv, h₁, h₂⟩ := mem_sem_add.mp (fapply.def (Expr.sem_pfunc _) hσ)
  obtain rfl : n₂ = 1 := Subtype.ext (mem_sem_lit.mp h₂).2
  refine ⟨n₁, n₁ + 1, (mem_sem_var.mp h₁).2, ?_, ?_⟩
  · rw [hv]
    exact pair_mem_override_self
  · transfer ZFNat → ℕ => omega

end Cmd

end Imp

end ZFSet

end

#print axioms ZFSet.Imp.Expr.mem_dom_sem_iff
#print axioms ZFSet.Imp.Cmd.sem_pfunc
#print axioms ZFSet.Imp.Cmd.sem_seq_assoc
#print axioms ZFSet.Imp.Cmd.assign_incr
