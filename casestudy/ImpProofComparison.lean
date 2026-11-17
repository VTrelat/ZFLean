module

public import Imp

/-!
# A matched comparison for applying two literal assignments

Both declarations below state the existing two-assignment application example from `Imp`.
They use exactly the same set-valued denotations and the same `fapply_composition` lemma.
The difference is how the functionality and domain certificates are supplied. The manual
declaration supplies every `fapply`/`fcomp` proof argument explicitly, bypassing the default
`autoParam` tactics, and supplies all domain-membership proofs by named lemmas.

This is a comparison of client certificate-writing, including theorem-statement elaboration,
not a whole-development productivity measurement. The proof body is the same in both cases.
The existing client lemma `Cmd.sem_assign_lit_isFunc` and library closure lemmas are shared.
-/

public noncomputable section

open ZFSet ZFSet.Imp ZFSet.Imp.Expr ZFSet.Imp.Cmd

namespace ImpProofComparison

variable {V : ZFSet}

theorem twoAssignments_auto (x y : V) (n m : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    @ᶻ(⟦assign y (lit m)⟧ᶜ ∘ᶻ ⟦assign x (lit n)⟧ᶜ) ⟨σ, by zdom⟩ =
      @ᶻ⟦assign y (lit m)⟧ᶜ ⟨(@ᶻ⟦assign x (lit n)⟧ᶜ ⟨σ, by zdom⟩).val, by zdom⟩ :=
  fapply_composition _ _ hσ

-- Disable the four tactics without falling back to their imported implementations.
@[no_fallback] local macro_rules
  | `(tactic| zrel) => `(tactic| fail "ZFLean automation disabled in manual comparison")
@[no_fallback] local macro_rules
  | `(tactic| zpfun) => `(tactic| fail "ZFLean automation disabled in manual comparison")
@[no_fallback] local macro_rules
  | `(tactic| zfun) => `(tactic| fail "ZFLean automation disabled in manual comparison")
@[no_fallback] local macro_rules
  | `(tactic| zdom) => `(tactic| fail "ZFLean automation disabled in manual comparison")

-- Check both a direct call and an implicit partial-functionality autoParam fail.
example (_x : V) (_n : ZFNat) : True := by
  fail_if_success zrel
  fail_if_success zpfun
  fail_if_success zfun
  fail_if_success zdom
  fail_if_success have applied := @ᶻ⟦assign _x (lit _n)⟧ᶜ
  trivial

theorem twoAssignments_manual (x y : V) (n m : ZFNat) {σ : ZFSet} (hσ : σ ∈ Store V) :
    let f := ⟦assign x (lit n)⟧ᶜ
    let g := ⟦assign y (lit m)⟧ᶜ
    let hf := sem_assign_lit_isFunc x n
    let hg := sem_assign_lit_isFunc y m
    let hpf := is_func_is_pfunc hf
    let hpg := is_func_is_pfunc hg
    let σf := fapply f hpf ⟨σ, mem_dom_of_mem hf hσ⟩
    fapply (fcomp g f hg hf) (IsPFunc_of_composition_IsPFunc hpf hpg)
      ⟨σ, mem_dom_of_mem (IsFunc_of_composition_IsFunc hg hf) hσ⟩ =
      fapply g hpg ⟨σf.val, mem_dom_of_mem hg σf.property⟩ :=
  fapply_composition _ _ hσ

-- Equality is homogeneous: this checks the two elaborated theorem types coincide.
example : @twoAssignments_auto = @twoAssignments_manual := rfl

#print axioms twoAssignments_auto
#print axioms twoAssignments_manual

end ImpProofComparison
