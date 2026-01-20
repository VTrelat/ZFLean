import ZFLean.Basic
import ZFLean.Booleans
import ZFLean.Integers
import ZFLean.Functions

namespace ZFSet

def Sum (A B : ZFSet) :=
  {x // x ∈ (ZFSet.prod { ZFBool.false.val } A) ∪ (ZFSet.prod { ZFBool.true.val } B)}
infixr:50 " ⊎ " => Sum

namespace Sum
def inl {A B : ZFSet} (a : {x // x ∈ A}) : Sum A B :=
  ⟨ZFSet.pair ZFBool.false a,
    mem_union.mpr (Or.inl <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, a.prop⟩)⟩
def inr {A B : ZFSet} (b : {x // x ∈ B}) : Sum A B :=
  ⟨ZFSet.pair ZFBool.true b,
    mem_union.mpr (Or.inr <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, b.prop⟩)⟩

theorem inl.injEq {A B : ZFSet} {x y : {x // x ∈ A}} : (inl x : A ⊎ B) = inl y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    rw [pair_inj] at heq
    exact Subtype.val_inj.mp heq.2
  · intro
    congr

theorem inr.injEq {A B : ZFSet} {x y : {x // x ∈ B}} : (inr x : A ⊎ B) = inr y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    rw [pair_inj] at heq
    exact Subtype.val_inj.mp heq.2
  · intro
    congr

theorem cases {A B : ZFSet} (x : A ⊎ B) : x.val.π₂ ∈ A ∨ x.val.π₂ ∈ B := by
  let ⟨x, hx⟩ := x
  rw [mem_union, mem_prod] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
  · rw [mem_union, pair_mem_prod] at hx
    obtain ⟨ha, bA⟩ | hb := hx
    · rw [mem_singleton] at ha
      left
      rwa [π₂_pair]
    · rw [pair_mem_prod, mem_singleton] at hb
      right
      rw [π₂_pair]
      exact hb.2
  · rw [mem_prod] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [mem_union, pair_mem_prod] at hx
    obtain ⟨ha, aB⟩ | hb := hx
    · rw [mem_singleton] at ha
      left
      rwa [π₂_pair]
    · rw [pair_mem_prod, mem_singleton] at hb
      right
      rw [π₂_pair]
      exact hb.2

@[cases_eliminator]
noncomputable def casesOn.{u, v} {A B : ZFSet.{u}} {motive : A ⊎ B → Sort v} (x : A ⊎ B)
  (inl : (val : {x // x ∈ A}) → motive (inl val))
  (inr : (val : {x // x ∈ B}) → motive (inr val)) : motive x := by
  by_cases h : x.val.π₁ = ZFBool.false.val
  · have : x.val.π₂ ∈ A := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rwa [π₂_pair]
      · dsimp at h
        rw [pair_eta hx, pair_mem_prod, mem_singleton, h] at hx
        nomatch zftrue_ne_zffalse hx.1.symm
    have : x = Sum.inl ⟨x.val.π₂, this⟩ := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [π₁_pair] at h
        subst a
        congr 2
        dsimp
        rw [π₂_pair]
      · rw [pair_eta hx, pair_mem_prod, mem_singleton, h] at hx
        nomatch zftrue_ne_zffalse hx.1.symm
    rw [this]
    apply inl
  · have x₁_eq_true : x.val.π₁ = ZFBool.true := by
      have := Subtype.property x
      rw [mem_union, mem_prod] at this
      obtain ⟨a, ha, b, hb, eq⟩ | hx := this
      · rw [eq, π₁_pair] at h
        rw [mem_singleton] at ha
        contradiction
      · rw [pair_eta hx, pair_mem_prod, mem_singleton] at hx
        exact hx.1
    have : x.val.π₂ ∈ B := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [mem_union, pair_mem_prod, mem_singleton] at hx
        obtain ⟨rfl, -⟩ | hb := hx
        · rw [π₁_pair] at x₁_eq_true
          nomatch zftrue_ne_zffalse x₁_eq_true.symm
        · rw [pair_mem_prod] at hb
          rw [π₂_pair]
          exact hb.2
      · rw [pair_eta hx, pair_mem_prod, mem_singleton] at hx
        exact hx.2
    have : x = Sum.inr ⟨x.val.π₂, this⟩ := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [mem_union, pair_mem_prod, mem_singleton] at hx
        obtain ⟨rfl, -⟩ | hb := hx
        · rw [π₁_pair] at x₁_eq_true
          nomatch zftrue_ne_zffalse x₁_eq_true.symm
        · congr 2
          · dsimp
            rwa [π₁_pair] at x₁_eq_true
          · dsimp
            rw [π₂_pair]
      · congr
        conv_lhs => rw [pair_eta hx]
        rw [pair_inj]
        exact ⟨x₁_eq_true, rfl⟩
    rw [this]
    apply inr

@[simp]
theorem casesOn_of_inl {A B : ZFSet} {motive : A ⊎ B → Sort*} (a : {x // x ∈ A})
  (inl_case : (val : {x // x ∈ A}) → motive (inl val))
  (inr_case : (val : {x // x ∈ B}) → motive (inr val)) :
    casesOn (inl a) inl_case inr_case = inl_case a := by
  rw [casesOn, dite_cond_eq_true (eq_true (by rw [inl, π₁_pair]))]
  dsimp
  rw [cast_eq_iff_heq]
  congr
  unfold inl
  rw [π₂_pair]

@[simp]
theorem casesOn_of_inr {A B : ZFSet} {motive : A ⊎ B → Sort*} (a : {x // x ∈ B})
  (inl_case : (val : {x // x ∈ A}) → motive (inl val))
  (inr_case : (val : {x // x ∈ B}) → motive (inr val)) :
    casesOn (inr a) inl_case inr_case = inr_case a := by
  rw [casesOn, dite_cond_eq_false (eq_false ?_)]
  · dsimp
    rw [cast_eq_iff_heq]
    congr
    unfold inr
    rw [π₂_pair]
  · rw [inr, π₁_pair]
    exact zftrue_ne_zffalse

noncomputable instance {A B : ZFSet} : A ⊎ B ≃ ({x // x ∈ A} ⊕ {x // x ∈ B}) where
  toFun x := by
    cases x with
    | inl a => exact _root_.Sum.inl a
    | inr b => exact _root_.Sum.inr b
  invFun x := by
    cases x with
    | inl a => exact inl a
    | inr b => exact inr b
  left_inv := by
    intro x
    cases x with
    | inl a =>
      beta_reduce
      conv_lhs => rw [casesOn_of_inl]
    | inr b =>
      beta_reduce
      conv_lhs => rw [casesOn_of_inr]
  right_inv := by
    intro x
    cases x with
    | inl a => simp only [casesOn_of_inl]
    | inr b => simp only [casesOn_of_inr]

end Sum

def Option (S : ZFSet) := {∅} ⊎ S

instance {T : ZFSet} : Nonempty (Option T) := ⟨Sum.inl ⟨∅, mem_singleton.mpr rfl⟩⟩

namespace Option
abbrev none {S : ZFSet} : Option S := Sum.inl ⟨∅, mem_singleton.mpr rfl⟩
abbrev some {S : ZFSet} (x : {x // x ∈ S}) : Option S := Sum.inr x

theorem some_ne_none {S : ZFSet} (x : {x // x ∈ S}) : some x ≠ none := by
  unfold some Sum.inr none Sum.inl
  intro h
  injection h with h
  rw [ZFSet.pair_inj] at h
  unfold ZFBool.false ZFBool.true zftrue zffalse at h
  obtain ⟨contr, _⟩ := h
  simp_rw [ZFSet.ext_iff, notMem_empty, iff_false, mem_singleton] at contr
  nomatch contr ∅

theorem casesOn {S : ZFSet} (x : Option S) : x = none ∨ (∃ y, x = some y) := by
  obtain ⟨x, hx⟩ := x
  rw [mem_union] at hx
  rcases hx with hx | hx <;> (
    rw [mem_prod] at hx
    obtain ⟨opt, hopt, val, hval, rfl⟩ := hx
    rw [mem_singleton] at hopt
    subst hopt
    rw [mem_union, pair_mem_prod] at hx)
  · left
    unfold none Sum.inl
    congr
    rcases hx with hx | hx
    · exact mem_singleton.mp hx.right
    · rw [pair_mem_prod, mem_singleton] at hx
      absurd hx.left
      unfold ZFBool.false ZFBool.true zftrue zffalse
      intro contr
      simp_rw [ZFSet.ext_iff, notMem_empty, false_iff, mem_singleton] at contr
      nomatch contr ∅
  · right
    rcases hx with hx | hx
    · rw [mem_singleton] at hx
      absurd hx.left
      unfold ZFBool.false ZFBool.true zftrue zffalse
      intro contr
      simp_rw [ZFSet.ext_iff, notMem_empty, iff_false, mem_singleton] at contr
      nomatch contr ∅
    · rw [pair_mem_prod] at hx
      unfold some Sum.inr
      exists ⟨val, hx.right⟩

-- theorem ZFInt.into.injective : Function.Injective into := into_inj
-- theorem ZFInt.outof.injective : Function.Injective outof := outof_inj

open Classical in
noncomputable abbrev the {S : ZFSet} (S_nemp : S ≠ ∅) (x : Option S) : {x // x ∈ S} :=
  if isNone : x = none then
    ⟨ε S, epsilon_spec (nonempty_exists_iff.mp S_nemp)⟩
  else choose (Or.resolve_left (casesOn x) isNone)


section ZFOption_to_Option

open Classical in
private noncomputable def into {T : ZFSet} : Option T → _root_.Option {x // x ∈ T} := fun x ↦
  if hx : x = none then .none else .some <| Classical.choose <| Or.resolve_left (casesOn x) hx

theorem some.injEq {T : ZFSet} {x y : {x // x ∈ T}} : some x = some y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    rw [pair_inj] at heq
    exact Subtype.val_inj.mp heq.2
  · intro
    congr

theorem ne_none_is_some {T : ZFSet} (x : Option T) : x ≠ none → ∃ y, x = some y := by
  intro h
  obtain ⟨y, hy⟩ := casesOn x
  · contradiction
  · assumption

theorem into.inj {T : ZFSet} :
    Function.Injective (into : Option T → _root_.Option {x // x ∈ T}) := by
  intro x y heq
  unfold into at heq
  split_ifs at heq with hx hy hy
  · rw [hx, hy]
  · injection heq with heq
    obtain ⟨x, rfl⟩ := ne_none_is_some x hx
    obtain ⟨y, rfl⟩ := ne_none_is_some y hy
    generalize_proofs px py at heq
    rw [Classical.choose_spec px, Classical.choose_spec py]
    congr

theorem into.surj {T : ZFSet} :
    Function.Surjective (into : Option T → _root_.Option {x // x ∈ T}) := by
  intro y
  unfold into
  cases y with
  | none =>
    exists none
    split_ifs <;> trivial
  | some v =>
    exists (some v)
    split_ifs with h
    · nomatch some_ne_none v h
    · generalize_proofs pv
      rw [← some.injEq.mp <| Classical.choose_spec pv]

theorem into.bij {T : ZFSet} :
  Function.Bijective (into : Option T → _root_.Option {x // x ∈ T}) := ⟨into.inj, into.surj⟩

noncomputable def EmbeddingZFOptionOption {T : ZFSet} : Option T ↪ _root_.Option {x // x ∈ T} where
  toFun := into
  inj' := into.inj

noncomputable instance instEquivZFOptionOption {T : ZFSet} :
    Option T ≃ _root_.Option {x // x ∈ T} where
  toFun := into
  invFun := Function.invFun into
  left_inv := Function.leftInverse_invFun into.inj
  right_inv := Function.rightInverse_invFun into.surj

end ZFOption_to_Option

section Option_to_ZFOption

private def outof {T : ZFSet} : _root_.Option {x // x ∈ T} → Option T
  | .some ⟨x, hx⟩ => some ⟨x, hx⟩
  | .none => none

theorem outof.inj {T : ZFSet} :
    Function.Injective (outof : _root_.Option {x // x ∈ T} → Option T) := by
  intro x y heq
  cases x <;> cases y <;> unfold outof at heq
  · rfl
  · injection heq with heq
    rw [pair_inj] at heq
    absurd heq.1
    unfold ZFBool.false ZFBool.true zftrue zffalse
    intro contr
    rw [Subtype.val_inj] at contr
    injection contr with contr
    rw [ZFSet.ext_iff] at contr
    exact (notMem_empty ∅) <| (mem_singleton.eq ▸ contr ∅).mpr rfl
  · injection heq with heq
    rw [pair_inj] at heq
    absurd heq.1
    unfold ZFBool.false ZFBool.true zftrue zffalse
    intro contr
    rw [Subtype.val_inj] at contr
    injection contr with contr
    rw [ZFSet.ext_iff] at contr
    exact (notMem_empty ∅) <| (mem_singleton.eq ▸ contr ∅).mp rfl
  · injection heq with heq
    rw [pair_inj] at heq
    have := Subtype.val_inj.mp <| Subtype.mk_eq_mk.mp <| Subtype.val_inj.mp heq.2
    congr

theorem outof.surj {T : ZFSet} :
    Function.Surjective (outof : _root_.Option {x // x ∈ T} → Option T) := by
  intro y
  unfold outof
  rcases y.casesOn with rfl | ⟨x, rfl⟩
  · exists .none
  · exists .some x

theorem outof.bij {T : ZFSet} :
  Function.Bijective (outof : _root_.Option {x // x ∈ T} → Option T) := ⟨outof.inj, outof.surj⟩

def EmbeddingOptionZFOption {T : ZFSet} : _root_.Option {x // x ∈ T} ↪ Option T where
  toFun := outof
  inj' := outof.inj

noncomputable instance instEquivOptionZFOption {T : ZFSet} :
    _root_.Option {x // x ∈ T} ≃ Option T where
  toFun := outof
  invFun := Function.invFun outof
  left_inv := Function.leftInverse_invFun outof.inj
  right_inv := Function.rightInverse_invFun outof.surj

end Option_to_ZFOption

abbrev toZFSet (T : ZFSet) :
  ZFSet := (ZFSet.prod { ZFBool.false.val } {∅}) ∪ (ZFSet.prod { ZFBool.true.val } T)

open Classical in
noncomputable def flift {A B : ZFSet} (f : ZFSet)
  (hf : IsFunc A B f := by zfun) :
    {f' : ZFSet // IsFunc (Option.toZFSet A) (Option.toZFSet B) f'} :=
  let f' : ZFSet :=
    λᶻ: Option.toZFSet A → Option.toZFSet B
      |          x       ↦ if hx : x ∈ Option.toZFSet A then
                              if isSome : ∃ y, ⟨x, hx⟩ = some y then
                                let ⟨y, hy⟩ := Classical.choose isSome
                                some (S := B) (@ᶻf ⟨y, by rwa [ZFSet.is_func_dom_eq]⟩) |>.val
                              else none (S := B).val
                            else ∅
  have hf' : IsFunc (Option.toZFSet A) (Option.toZFSet B) f' := by
    apply ZFSet.lambda_isFunc
    intro x hx
    rw [dite_cond_eq_true (eq_true hx)]
    split_ifs with isSome <;> apply SetLike.coe_mem
  ⟨f', hf'⟩

theorem flift_bijective {f A B : ZFSet} (hf : IsFunc A B f) :
    (ZFSet.Option.flift f).val.IsBijective (Subtype.property _) ↔ f.IsBijective hf where
  mp := by
    rintro ⟨hinj, hsurj⟩
    and_intros
    · intro x y z hx hy hz xz yz
      specialize hinj (Option.some ⟨x, hx⟩).val (Option.some ⟨y, hy⟩).val (Option.some ⟨z, hz⟩).val
        (SetLike.coe_mem _) (SetLike.coe_mem _) (SetLike.coe_mem _) ?_ ?_
      · rw [flift, lambda_spec]
        simp only [SetLike.coe_mem, ↓reduceDIte, Subtype.coe_eta, some.injEq, exists_eq',
          Classical.choose_eq', SetLike.coe_eq_coe, true_and]
        rw [Option.some.injEq]
        symm
        exact fapply.of_pair _ xz
      · rw [flift, lambda_spec]
        simp only [SetLike.coe_mem, ↓reduceDIte, Subtype.coe_eta, some.injEq, exists_eq',
          Classical.choose_eq', SetLike.coe_eq_coe, true_and]
        rw [Option.some.injEq]
        symm
        exact fapply.of_pair _ yz
      · rwa [←Subtype.ext_iff, Option.some.injEq, Subtype.ext_iff] at hinj
    · intro y hy
      have : (Option.some ⟨y, hy⟩).val ∈ Option.toZFSet B :=
        SetLike.coe_mem _
      obtain ⟨x, hx, xy⟩ := hsurj _ this
      rw [flift, lambda_spec, dite_cond_eq_true (eq_true hx)] at xy
      obtain ⟨-, -, eq⟩ := xy
      split_ifs at eq with issome
      · rw [←Subtype.ext_iff, Option.some.injEq, Subtype.ext_iff] at eq
        obtain rfl := eq
        use (Classical.choose issome).val
        and_intros
        · apply SetLike.coe_mem
        · apply fapply.def
      · rw [←Subtype.ext_iff] at eq
        nomatch ZFSet.Option.some_ne_none _ eq
  mpr := by
    intro hbij
    rw [bijective_exists1_iff] at hbij ⊢
    intro y hy
    obtain eq | ⟨⟨y, hy⟩, eq⟩ := Option.casesOn ⟨y, hy⟩ <;>
      (rw [Subtype.ext_iff] at eq; obtain rfl := eq)
    · use (@none A).val
      and_intros
      · apply SetLike.coe_mem
      · rw [flift, lambda_spec, dite_cond_eq_true (eq_true (SetLike.coe_mem _))]
        and_intros
        · apply SetLike.coe_mem
        · apply SetLike.coe_mem
        · split_ifs with isnone
          · obtain ⟨_, contr⟩ := isnone
            change none = some _ at contr
            nomatch ZFSet.Option.some_ne_none _ contr.symm
          · rfl
      · rintro y ⟨hy, pair⟩
        rw [flift, lambda_spec] at pair
        obtain ⟨-, -, eq⟩ := pair
        rw [dite_cond_eq_true (eq_true hy)] at eq
        split_ifs at eq with issome
        · rw [←Subtype.ext_iff] at eq
          nomatch ZFSet.Option.some_ne_none _ eq.symm
        · have := @ZFSet.Option.ne_none_is_some _ ⟨y, hy⟩
          rwa [imp_iff_not issome, not_not, Subtype.ext_iff] at this
    · obtain ⟨x, ⟨hx, fxy⟩, x_unq⟩ := hbij y ‹_›
      use (Option.some ⟨x, hx⟩).val
      and_intros
      · apply SetLike.coe_mem
      · rw [flift, lambda_spec, dite_cond_eq_true (eq_true (SetLike.coe_mem _))]
        and_intros
        · apply SetLike.coe_mem
        · apply SetLike.coe_mem
        · split_ifs with isnone
          · have := Classical.choose_spec isnone
            change some _ = some _ at this
            rw [Option.some.injEq, Subtype.ext_iff] at this
            dsimp at this
            rw [←Subtype.ext_iff, Option.some.injEq, eq_comm]
            apply fapply.of_pair
            rwa [this] at fxy
          · simp only [Subtype.coe_eta, exists_apply_eq_apply', not_true_eq_false] at isnone
      · rintro z ⟨hz, fzy⟩
        rw [flift, lambda_spec] at fzy
        obtain ⟨-, -, eq⟩ := fzy
        rw [dite_cond_eq_true (eq_true hz)] at eq
        split_ifs at eq with issome
        · rw [←Subtype.ext_iff, Option.some.injEq, Subtype.ext_iff] at eq
          obtain rfl := eq
          have := Classical.choose_spec issome
          rw [Subtype.ext_iff] at this
          dsimp at this
          rw [this, ←Subtype.ext_iff, Option.some.injEq]
          have := fapply.of_pair (is_func_is_pfunc hf) fxy
          simp only [Subtype.coe_eta] at this
          rw [←bijective_exists1_iff hf] at hbij
          symm
          have := IsInjective.apply_inj hf hbij.1 this
          rwa [Subtype.ext_iff] at this ⊢
        · rw [←Subtype.ext_iff] at eq
          nomatch ZFSet.Option.some_ne_none _ eq

end Option

end ZFSet
