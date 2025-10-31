import ZFLean.Rationals
import ZFLean.Booleans
import ZFLean.Tactics

namespace ZFSet
set_option linter.unusedVariables false

section Relations

-- syntax "zrel" : tactic
-- macro_rules | `(tactic| zrel) => `(tactic| (
--   change ?R ⊆ ZFSet.prod ?A ?B
--   try
--     have : ZFSet.IsFunc ?A ?B ?R := by try assumption
--     obtain ⟨_,_⟩ := this
--   exact ‹?R ⊆ ZFSet.prod ?A ?B›))

/--
Inverse of a (binary) relation. A proof that `R` is a relation is needed and tried to be
automatically inferred.
-/
def inv (R : ZFSet) {A B : ZFSet} (isRel : R ⊆ A.prod B := by zrel) : ZFSet :=
  (B.prod A).sep fun yx ↦
    let x := yx.π₂
    let y := yx.π₁
    x.pair y ∈ R

postfix:max "⁻¹" => inv

theorem mem_inv {x y R A B : ZFSet} (hR : R ⊆ A.prod B) :
    y.pair x ∈ R⁻¹ ↔ x.pair y ∈ R where
  mp := by
    intro h
    dsimp [inv] at h
    rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair] at h
    exact h.2
  mpr := by
    intro h
    rw [inv, mem_sep, pair_mem_prod, π₁_pair, π₂_pair]
    dsimp
    and_intros
    · exact hR h |> pair_mem_prod.mp |>.2
    · exact hR h |> pair_mem_prod.mp |>.1
    · exact h

@[zrel]
theorem subset_prod_inv {R A B : ZFSet} (hR : R ⊆ A.prod B) : R⁻¹ ⊆ B.prod A := by
  intro z hz
  rw [inv, mem_sep] at hz
  exact hz.1

-- macro_rules | `(tactic| zrel) => `(tactic| apply subset_prod_inv; done)

theorem inv_involutive {R A B : ZFSet} (hR : R ⊆ A.prod B) : (R⁻¹)⁻¹ = R := by
  ext1 z
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := (subset_prod_inv <| subset_prod_inv hR) h |> mem_prod.mp
    rwa [mem_inv, mem_inv] at h
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := hR h |> mem_prod.mp
    rwa [mem_inv, mem_inv]

/--
Domain of a (binary) relation. A proof that `f` is a relation is needed and tried to be
automatically inferred.
-/
-- abbrev Dom   (f : ZFSet) {A B : ZFSet} (hf : f ⊆ A.prod B := by zrel) :=
--   ⋃₀ (A.powerset.sep λ 𝒟 => IsFunc 𝒟 B f) --NOTE: this def was specific to functions
abbrev Dom (f : ZFSet) {A B : ZFSet} (hf : f ⊆ A.prod B := by zrel) :=
  A.sep (fun x => ∃ y ∈ B, pair x y ∈ f)

abbrev Range (f : ZFSet) {A B : ZFSet} (hf : f ⊆ A.prod B := by zrel) :=
  B.sep (fun y => ∃ x ∈ Dom f hf, pair x y ∈ f)

end Relations

section Functions

theorem funs.nonempty {A B : ZFSet} (hB : B ≠ ∅) : ZFSet.funs A B ≠ ∅ := by
  obtain ⟨b, hb⟩ := nonempty_exists_iff.mp hB
  letI f := (A.prod B).sep fun z ↦ ∃ x ∈ A, z = x.pair b
  have hf : ZFSet.IsFunc A B f := by
    unfold IsFunc
    and_intros
    · exact sep_subset_self
    · intro x hx
      exists b
      and_intros
      · beta_reduce
        rw [mem_sep, pair_mem_prod]
        exact ⟨⟨hx,hb⟩,x, ⟨hx, rfl⟩⟩
      · intro y hy
        rw [mem_sep, pair_mem_prod] at hy
        obtain ⟨⟨xA, yB⟩, z, z_A, eq⟩ := hy
        rw [pair_inj] at eq
        exact eq.2
  intro contr
  rw [← mem_funs, contr] at hf
  nomatch notMem_empty f hf

/--
`IsPFunc f A B` is the assertion that `f` is a partial function from `A` to `B`,
i.e. that if `pair x y ∈ f` and `pair x z ∈ f` then `y = z`.
-/
def IsPFunc (f A B : ZFSet) := f ⊆ prod A B ∧ ∀ x y :
  ZFSet, pair x y ∈ f → ∀ z, pair x z ∈ f → y = z

-- syntax "zpfun" : tactic
-- macro_rules | `(tactic| zpfun) => `(tactic| assumption; done)

-- syntax "zfun" : tactic
-- macro_rules | `(tactic| zfun) => `(tactic| assumption; done)

-- macro_rules | `(tactic| zrel) => `(tactic| first | zfun | zpfun)

@[zrel]
theorem is_rel_of_is_pfunc {f A B : ZFSet} (hf : f.IsPFunc A B) : f ⊆ A.prod B := hf.1

-- macro_rules | `(tactic| zrel) => `(tactic| (
--   change ?R ⊆ ZFSet.prod ?A ?B
--   try
--     have : IsPFunc ?R ?A ?B := by try assumption
--     obtain ⟨_,_⟩ := this
--   exact ‹?R ⊆ ZFSet.prod ?A ?B›))

-- macro_rules | `(tactic| zrel) => `(tactic| apply is_rel_of_is_pfunc; assumption; done)

theorem pfunc_weaken {f A B C D : ZFSet} (hf : f.IsPFunc C D) (hAB : C ⊆ A) (hCD : D ⊆ B) :
    f.IsPFunc A B := by
  rcases hf with ⟨sub, unique⟩
  and_intros
  · intro _ hz
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_prod.mp <| sub hz
    rw [mem_prod]
    exact ⟨a, hAB ha, b, hCD hb, rfl⟩
  · intros x y pair_x_y z pair_x_z
    exact unique x y pair_x_y z pair_x_z

-- macro_rules | `(tactic| zpfun) =>
--   `(tactic| (apply pfunc_weaken <;> first | (assumption; done) | zpfun))

@[zpfun]
theorem is_func_is_pfunc {f A B : ZFSet} (hf : A.IsFunc B f) : f.IsPFunc A B := by
  obtain ⟨sub, func⟩ := hf
  and_intros
  · assumption
  · intros x y pair_x_y z pair_x_z
    obtain ⟨_, x_A, b, b_B, eq⟩ := mem_prod.mp <| sub pair_x_y
    rw [pair_inj] at eq; rcases eq with ⟨rfl, rfl⟩
    obtain ⟨w, pair_x_w, unique⟩ := func x x_A
    rw [unique z pair_x_z, unique y pair_x_y]

-- macro_rules | `(tactic| zpfun) => `(tactic| apply is_func_is_pfunc; zfun; done)

@[zrel]
theorem is_rel_of_is_func {f A B : ZFSet} (hf : A.IsFunc B f) : f ⊆ A.prod B := hf.1

-- macro_rules | `(tactic| zrel) => `(tactic| apply is_rel_of_is_func; zfun; done)

theorem is_func_extend_range {f D E : ZFSet} (hf : IsFunc D E f) {F : ZFSet} (sub_E_F : E ⊆ F) :
    IsFunc D F f := by
  rcases hf with ⟨sub, func⟩
  and_intros
  · intro _ hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.mp <| sub hz
    rw [mem_prod]
    exact ⟨a, ha, b, sub_E_F hb, rfl⟩
  · exact func

-- macro_rules | `(tactic| zpfun) =>
--   `(tactic| apply is_func_extend_range <;> first | (assumption;done) | zpfun)

@[simp, zfun]
theorem is_func_empty : IsFunc ∅ ∅ ∅ :=
  ⟨empty_subset (prod ∅ ∅), fun _ h ↦ nomatch h, notMem_empty _⟩

theorem is_pfunc_func_exists {f A B : ZFSet} :
    f.IsPFunc A B → ∃ A' B', IsFunc A' B' f ∧ A' ⊆ A ∧ B' ⊆ B := by
  classical
  rintro ⟨sub_AB, func⟩
  by_cases hf : f = ∅
  · subst f
    exact ⟨∅, ∅, is_func_empty, empty_subset A, empty_subset B⟩
  · let A' := A.sep (fun x ↦ ∃ y, pair x y ∈ f)
    let B' := B.sep (fun y ↦ ∃ x ∈ A', pair x y ∈ f)
    exists A', B'
    and_intros
    · intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.mp <| sub_AB hz
      rw [mem_prod]
      unfold A' B'
      simp only [mem_sep]
      exists a
      and_intros
      · exact ha
      · exact ⟨b, hz⟩
      · exact ⟨b, ⟨hb, a, mem_sep.mpr ⟨ha, b, hz⟩, hz⟩, rfl⟩
    · intro x x_A
      rw [mem_sep] at x_A
      obtain ⟨x_A, y, pair⟩ := x_A
      have y_B : y ∈ B := by
        obtain ⟨_,_,_,_,h⟩ := mem_prod.mp <| sub_AB pair
        rw [pair_inj] at h
        rcases h with ⟨rfl, rfl⟩
        assumption
      exact ⟨y, pair, fun z hz ↦ func x z hz y pair⟩
    repeat (intro z hz; exact mem_sep.mp hz |>.left)

theorem pfun_dom_subset (f : ZFSet) {A B} (hf : f.IsPFunc A B) : f.Dom ⊆ A := by
  rintro x x_dom
  rw [mem_sep] at x_dom
  exact x_dom.1

theorem mem_dom {f A B : ZFSet} (hf : f.IsPFunc A B) {x y : ZFSet} :
    pair x y ∈ f → x ∈ f.Dom := by classical
  intro mem_pair
  obtain ⟨D, C, is_func_DC, Dsub, Csub⟩ := is_pfunc_func_exists hf
  rcases hf with ⟨sub, unique⟩
  obtain ⟨a, ha, b, hb, eq⟩ := mem_prod.mp <| sub mem_pair
  rw [pair_inj] at eq
  rcases eq with ⟨rfl, rfl⟩
  rw [mem_sep]
  and_intros
  · exact ha
  · use y

theorem is_func_dom_range (f : ZFSet) {A B} (hf : f.IsPFunc A B) :
    IsFunc f.Dom f.Range f := by
  classical
  rcases hf with ⟨sub, unique⟩
  and_intros
  · intro _ h
    obtain ⟨a,a_A,b,b_B,rfl⟩ := mem_prod.mp <| sub h
    rw [pair_mem_prod]
    and_intros
    · rw [mem_sep]
      and_intros
      · exact a_A
      · use b
    · unfold Range
      rw [mem_sep]
      and_intros
      · exact b_B
      · exists a
        and_intros
        · exact mem_dom ⟨sub, unique⟩ h
        · exact h
  · intro z z_dom
    rw [mem_sep] at z_dom
    obtain ⟨zA, w, hw, zw_f⟩ := z_dom
    use w
    and_intros
    · exact zw_f
    · intro w' zw'_f
      exact unique z w' zw'_f w zw_f

theorem is_func_of_pfunc (f : ZFSet) {A B} (hf : f.IsPFunc A B) : IsFunc f.Dom B f := by
  obtain ⟨ftot, uniq⟩ := is_func_dom_range f hf
  obtain ⟨fsub, ispfun⟩ := hf
  and_intros
  · intro z hz
    obtain ⟨x, xA, y, yB, rfl⟩ := mem_prod.mp <| fsub hz
    obtain ⟨u, u_dom, v, v_dom, eq⟩ := mem_prod.mp <| ftot hz
    rcases pair_inj.mp eq with ⟨rfl, rfl⟩
    clear eq
    rw [pair_mem_prod]
    exact ⟨u_dom, yB⟩
  · exact uniq

def IsInjective (f : ZFSet) {A B : ZFSet} (hf : IsFunc A B f := by zfun) :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ B → x.pair z ∈ f → y.pair z ∈ f → x = y

def IsSurjective (f : ZFSet) {A B : ZFSet} (hf : IsFunc A B f := by zfun) :=
  ∀ y ∈ B, ∃ x ∈ A, x.pair y ∈ f

def IsBijective (f : ZFSet) {A B : ZFSet} (hf : IsFunc A B f := by zfun) :=
  f.IsInjective ∧ f.IsSurjective

theorem bijective_exists1_iff {f A B : ZFSet} (hf : IsFunc A B f) :
  f.IsBijective ↔ ∀ y ∈ B, ∃! x ∈ A, x.pair y ∈ f := by
  constructor
  · intro bij y y_B
    obtain ⟨inj, surj⟩ := bij
    obtain ⟨x, x_A, x_pair_y⟩ := surj y y_B
    apply ExistsUnique.intro x ⟨x_A, x_pair_y⟩
    rintro z ⟨z_A, z_pair_y⟩
    exact inj x z y x_A z_A y_B x_pair_y z_pair_y |>.symm
  · intro exists1
    constructor
    · intro x z y x_A z_A y_B x_pair_y z_pair_y
      obtain ⟨w, ⟨w_A, w_pair_y⟩, unique⟩ := exists1 y y_B
      rw [unique x ⟨x_A, x_pair_y⟩, unique z ⟨z_A, z_pair_y⟩]
    · intro y y_B
      obtain ⟨x, ⟨x_A, x_pair_y⟩, unique⟩ := exists1 y y_B
      exact ⟨x, x_A, x_pair_y⟩

def IsMono {f A B : ZFSet}
  [LTA : Preorder {x // x ∈ A}]
  [LTB : Preorder {x // x ∈ B}]
  (_ : IsFunc A B f) :=
  ∀ x₁ x₂ y₁ y₂,
    (x₁_A : x₁ ∈ A) →
    (y₁_B :y₁ ∈ B) →
    x₁.pair y₁ ∈ f →
    (x₂_A : x₂ ∈ A) →
    (y₂_B : y₂ ∈ B) →
    x₂.pair y₂ ∈ f →
    LTA.le ⟨x₁, x₁_A⟩ ⟨x₂, x₂_A⟩ →
    LTB.le ⟨y₁, y₁_B⟩ ⟨y₂, y₂_B⟩

def IsStrictMono {f A B : ZFSet}
  [LTA : Preorder {x // x ∈ A}]
  [LTB : Preorder {x // x ∈ B}]
  (_ : IsFunc A B f) :=
  ∀ x₁ x₂ y₁ y₂,
    (x₁_A : x₁ ∈ A) →
    (y₁_B :y₁ ∈ B) →
    x₁.pair y₁ ∈ f →
    (x₂_A : x₂ ∈ A) →
    (y₂_B : y₂ ∈ B) →
    x₂.pair y₂ ∈ f →
    LTA.lt ⟨x₁, x₁_A⟩ ⟨x₂, x₂_A⟩ →
    LTB.lt ⟨y₁, y₁_B⟩ ⟨y₂, y₂_B⟩

def Id (A : ZFSet) : ZFSet :=
  (A.prod A).sep fun x => ∃ y : ZFSet, y ∈ A ∧ x = y.pair y
prefix:max "𝟙" => Id

theorem pair_mem_Id_iff {A : ZFSet} {x y : ZFSet} (hx : x ∈ A) : x.pair y ∈ 𝟙A ↔ x = y := by
  simp only [Id, mem_sep, mem_prod, pair_inj, exists_eq_right_right', and_assoc]
  constructor
  · rintro ⟨_, _, _, _, rfl⟩
    rfl
  · rintro rfl
    simpa only [and_true, and_self]

theorem mem_Id_iff {A : ZFSet} {z : ZFSet} : z ∈ 𝟙A ↔ ∃ x ∈ A, z = x.pair x := by
  simp only [Id, mem_sep, mem_prod, and_iff_right_iff_imp, forall_exists_index, and_imp]
  rintro x xA rfl
  use x, xA, x, xA

theorem pair_self_mem_Id {A : ZFSet} {x : ZFSet} (hx : x ∈ A) : x.pair x ∈ 𝟙A := by
  rwa [pair_mem_Id_iff]

@[zfun]
theorem Id.IsFunc {A : ZFSet} : A.IsFunc A 𝟙A := by
  unfold Id
  and_intros
  · intro z hz
    rw [mem_sep] at hz
    exact hz.1
  · intro x xA
    simp only [mem_sep, mem_prod, pair_inj, exists_eq_right_right']
    exists x
    beta_reduce
    simp only [and_self, and_true, and_imp, forall_self_imp]
    and_intros
    · exact xA
    · rintro _ _ _ rfl
      rfl

-- macro_rules | `(tactic| zfun) => `(tactic| apply Id.IsFunc; done)

@[zpfun]
theorem Id.IsPFunc {A : ZFSet} : (𝟙A).IsPFunc A A := is_func_is_pfunc IsFunc

-- macro_rules | `(tactic| zpfun) => `(tactic| apply Id.IsPFunc; done)

theorem Id.IsBijective {A : ZFSet} : (𝟙A).IsBijective Id.IsFunc := by
  constructor
  · intro x y z xA yA zA x_pair_y y_pair_z
    rw [Id, mem_sep, pair_mem_prod] at x_pair_y y_pair_z
    obtain ⟨x', x'_A, eq_x⟩ := x_pair_y.2
    obtain ⟨y', y'_A, eq_y⟩ := y_pair_z.2
    rw [pair_inj] at eq_x eq_y
    obtain ⟨rfl, rfl⟩ := eq_x
    obtain ⟨rfl, rfl⟩ := eq_y
    rfl
  · intro y yA
    simp_rw [Id, mem_sep, pair_mem_prod, pair_inj, exists_eq_right_right',
      existsAndEq, and_self, yA, and_true]

def IsPermutation (σ E : ZFSet) := ∃ (hσ : E.IsFunc E σ), σ.IsBijective

def permutations (E : ZFSet) : ZFSet := (E.funs E).sep fun f => f.IsPermutation E

theorem Id.IsPermutation {A : ZFSet} : IsPermutation 𝟙A A := by
  exists Id.IsFunc
  exact Id.IsBijective

/--
If `f : A → B` and `g : B → C` are functions, then `composition g f` is the function
from `A` to `C` defined by `composition g f (x, z) = (x, y)` where `y` is such that
`(x, y) ∈ f` and `(y, z) ∈ g`.
-/
def composition (g f : ZFSet) (A B C : ZFSet) : ZFSet :=
  (A.prod C).sep fun xz =>
    ∃ (x z : ZFSet), xz = x.pair z ∧ ∃ y ∈ B, x.pair y ∈ f ∧ y.pair z ∈ g

theorem mem_composition (g f : ZFSet) {A B C : ZFSet} {z : ZFSet} :
  z ∈ composition g f A B C ↔
    ∃ (x w y : ZFSet), z = x.pair y ∧ x ∈ A ∧ y ∈ C ∧ w ∈ B ∧ x.pair w ∈ f ∧ w.pair y ∈ g := by
  simp only [composition, mem_sep, mem_prod]
  constructor
  · rintro ⟨⟨a, ha, c, hc, rfl⟩, ⟨_, _, eq, _, memB, memf, memg⟩⟩
    rw [pair_inj] at eq
    obtain ⟨rfl, rfl⟩ := eq
    simp only [pair_inj, existsAndEq, and_true, exists_and_left, exists_eq_left']
    and_intros
    · exact ha
    · exact hc
    · exact ⟨_, memB, memf, memg⟩
  · rintro ⟨x, w, y, rfl, xA, yC, wB, xw_f, wy_g⟩
    simp only [pair_inj, exists_eq_right_right', existsAndEq, and_true, exists_eq_left']
    and_intros
    · exact xA
    · exact yC
    · exact ⟨w, wB, xw_f, wy_g⟩

theorem Id.composition_left {f A B : ZFSet} (hf : f ⊆ A.prod B) : composition 𝟙B f A B B = f := by
  ext1 x
  unfold Id composition
  simp only [mem_sep, mem_prod, pair_inj, exists_eq_right_right', existsAndEq, and_self, and_true]
  constructor
  · rintro ⟨⟨a, aA, b, bB, rfl⟩, x, y, eq, yB, memf, -⟩
    rw [pair_inj] at eq
    obtain ⟨rfl, rfl⟩ := eq
    exact memf
  · intro xf
    and_intros
    · obtain ⟨a, aA, b, bB, rfl⟩ := mem_prod.mp <| hf xf
      exists a, aA, b, bB
    · obtain ⟨a, aA, b, bB, rfl⟩ := mem_prod.mp <| hf xf
      exists a, b

theorem Id.composition_right {f A B : ZFSet} (hf : f ⊆ A.prod B) : composition f 𝟙A A A B = f := by
  ext1 x
  unfold Id composition
  simp only [mem_sep, mem_prod, pair_inj, exists_eq_right_right', existsAndEq, and_self, and_true]
  constructor
  · rintro ⟨⟨a, aA, b, bB, rfl⟩, x, y, eq, xB, xA, memf⟩
    rw [pair_inj] at eq
    obtain ⟨rfl, rfl⟩ := eq
    exact memf
  · intro xf
    and_intros
    · obtain ⟨a, aA, b, bB, rfl⟩ := mem_prod.mp <| hf xf
      exists a, aA, b, bB
    · obtain ⟨a, aA, b, bB, rfl⟩ := mem_prod.mp <| hf xf
      exists a, b

@[zpfun]
theorem IsPFunc_of_composition_IsPFunc {f g : ZFSet} {A B C : ZFSet}
  (hf : f.IsPFunc A B) (hg : g.IsPFunc B C) :
    (composition g f A B C).IsPFunc A C := by
  and_intros
  · intro z hz
    rw [composition, mem_sep] at hz
    exact hz.1
  · intro x y hxy z hz
    rw [composition, mem_sep, pair_mem_prod] at hxy hz
    obtain ⟨a, c, eq, b, bB, ab_f, bc_g⟩ := hz.2
    obtain ⟨a', c', eq', b', bB', ab_f', bc_g'⟩ := hxy.2
    rw [pair_inj] at eq eq'
    obtain ⟨rfl, rfl⟩ := eq
    obtain ⟨rfl, rfl⟩ := eq'
    have := hf.2 _ _ ab_f _ ab_f'
    subst this
    symm
    exact hg.2 _ _ bc_g _ bc_g'

-- macro_rules | `(tactic| zpfun) =>
--   `(tactic| apply IsPFunc_of_composition_IsPFunc <;> first | (assumption; done) | zpfun)

@[zfun]
theorem IsFunc_of_composition_IsFunc {g f : ZFSet} {A B C : ZFSet}
  (hg : B.IsFunc C g) (hf : A.IsFunc B f) :
    A.IsFunc C (composition g f A B C) := by
  and_intros
  · intro z hz
    rw [composition, mem_sep] at hz
    exact hz.1
  · intro x xA
    obtain ⟨y, xy_f, y_unq⟩ := hf.2 x xA
    have yB : y ∈ B := And.right <| pair_mem_prod.mp <| hf.1 xy_f
    obtain ⟨z, yz_g, z_unq⟩ := hg.2 y yB
    have zC : z ∈ C := And.right <| pair_mem_prod.mp <| hg.1 yz_g
    exists z
    simp_rw [composition, mem_sep, pair_mem_prod]
    and_intros
    · exact xA
    · exact zC
    · exists x, z
      and_intros
      · rfl
      · exists y
    · intro z' hz'
      obtain ⟨x', z', eq, y', y'_B, x'y'f, y'z'g⟩ := hz'.2
      rw [pair_inj] at eq
      obtain ⟨rfl, rfl⟩ := eq
      apply z_unq
      suffices y' = y by
        rw [←this]
        exact y'z'g
      apply y_unq
      exact x'y'f

-- macro_rules | `(tactic| zfun) =>
--   `(tactic| apply IsFunc_of_composition_IsFunc <;> first | (assumption; done) | zfun)

abbrev fcomp (g f : ZFSet) {A B C : ZFSet}
  (hg : B.IsFunc C g := by zfun) (hf : A.IsFunc B f := by zfun) :=
    composition g f A B C
infixl:90 " ∘ᶻ " => fcomp

theorem IsInjective.composition_of_injective {f g : ZFSet} {A B C : ZFSet}
  {hf : A.IsFunc B f} {hg : B.IsFunc C g}
  (finj : f.IsInjective) (ginj : g.IsInjective) :
    (g ∘ᶻ f).IsInjective := by
  intro x y z xA yA zC x_f y_f
  rw [fcomp, composition, mem_sep, pair_mem_prod] at x_f y_f
  obtain ⟨a, c, eq, b, bB, ab_f, bc_g⟩ := x_f.2
  have cC : c ∈ C := And.right <| pair_mem_prod.mp <| hg.1 bc_g
  obtain ⟨a', c', eq', b', bB', a'b_f, b'c_g⟩ := y_f.2
  have cC' : c' ∈ C := And.right <| pair_mem_prod.mp <| hg.1 b'c_g
  rw [pair_inj] at eq eq'
  obtain ⟨rfl, rfl⟩ := eq
  obtain ⟨rfl, rfl⟩ := eq'
  obtain ⟨rfl⟩ := ginj _ _ _ bB bB' cC bc_g b'c_g
  exact finj _ _ _ xA yA bB ab_f a'b_f

theorem IsSurjective.composition_of_surjective {f g : ZFSet} {A B C : ZFSet}
  {hf : A.IsFunc B f} {hg : B.IsFunc C g}
  (fsurj : f.IsSurjective) (gsurj : g.IsSurjective) :
    (g ∘ᶻ f).IsSurjective := by
  intro z zC
  simp only [composition, mem_sep, pair_mem_prod, pair_inj, existsAndEq, and_true, exists_eq_left']
  obtain ⟨y, hy, yz_g⟩ := gsurj z zC
  obtain ⟨x, xA, xy_f⟩ := fsurj y hy
  exists x
  and_intros
  · exact xA
  · exact xA
  · exact zC
  · exists y

theorem IsBijective.composition_of_bijective {f g : ZFSet} {A B C : ZFSet}
  {hf : A.IsFunc B f} {hg : B.IsFunc C g}
  (fbij : f.IsBijective) (gbij : g.IsBijective) :
    (g ∘ᶻ f).IsBijective :=
  ⟨IsInjective.composition_of_injective fbij.1 gbij.1,
    IsSurjective.composition_of_surjective fbij.2 gbij.2⟩

theorem IsPermutation.composition_of_permutations {σ τ : ZFSet} {E : ZFSet}
  (hσ : σ.IsPermutation E) (hτ : τ.IsPermutation E) :
    (composition τ σ E E E).IsPermutation E := ⟨
  IsFunc_of_composition_IsFunc hτ.1 hσ.1,
  IsInjective.composition_of_injective hσ.2.1 hτ.2.1,
  IsSurjective.composition_of_surjective hσ.2.2 hτ.2.2⟩

open Classical in
noncomputable def fapply (f : ZFSet) {A B : ZFSet} (hf : f.IsPFunc A B := by zpfun) :
  {x // x ∈ f.Dom} → {x // x ∈ B} := fun ⟨x, x_dom⟩ ↦
  have : ∃ y ∈ B, pair x y ∈ f := by
    unfold Dom at x_dom
    rw [mem_sep] at x_dom
    obtain ⟨xA, y, yB, xyf⟩ := x_dom
    use y
  ⟨choose this, choose_spec this |>.left⟩

notation:max "@ᶻ" f:max => fapply f

@[simp]
theorem is_func_dom_eq {f A B : ZFSet} (hf : IsFunc A B f := by zfun) : f.Dom = A := by
  ext1 x
  constructor
  · intro x_dom
    rw [mem_sep] at x_dom
    obtain ⟨xA⟩ := x_dom
    exact xA
  · intro mem_x_A
    rw [mem_sep]
    and_intros
    · exact mem_x_A
    · obtain ⟨y, hy, _⟩ := hf.2 x mem_x_A
      use y
      and_intros
      · exact hf.1 hy |> pair_mem_prod.mp |>.2
      · exact hy

open Classical in
theorem fapply_Id {A x : ZFSet} (hx : x ∈ A) :
    @ᶻ𝟙A ⟨x, by rwa [is_func_dom_eq Id.IsFunc]⟩ = ⟨x, hx⟩ := by
  rw [fapply]
  generalize_proofs choose _
  obtain ⟨_, mem_id⟩ := choose_spec choose
  rw [pair_mem_Id_iff hx] at mem_id
  congr
  rw [←mem_id]

theorem fapply_mem_range {f A B : ZFSet} (hf : f.IsPFunc A B) {x : ZFSet} (hx : x ∈ f.Dom) :
    (@ᶻf ⟨x, hx⟩).val ∈ B := by
  apply Subtype.property

theorem fapply.def {f A B : ZFSet} (hf : f.IsPFunc A B) {x : ZFSet} (hx : x ∈ f.Dom) :
  x.pair (@ᶻf ⟨x, hx⟩) ∈ f := by
  dsimp [fapply]
  generalize_proofs y_def
  exact Classical.choose_spec y_def |>.2

theorem IsInjective.apply_inj {f A B : ZFSet} (hf : IsFunc A B f) (inj : f.IsInjective) :
    Function.Injective @ᶻf := by classical
  rintro ⟨x, x_dom⟩ ⟨y, y_dom⟩ h
  have x_A : x ∈ A := by rwa [is_func_dom_eq hf] at x_dom
  have y_A : y ∈ A := by rwa [is_func_dom_eq hf] at y_dom
  obtain ⟨pair_x_ε, unq_fx⟩ := Classical.choose_spec <| hf.right x x_A
  obtain ⟨pair_y_ε, unq_fy⟩ := Classical.choose_spec <| hf.right y y_A
  congr
  unfold fapply at h
  injection h with h
  generalize_proofs hpf hpf' at h
  have choose_eq {z} (z_dom : z ∈ f.Dom) :
      Classical.choose (hf.right z (is_func_dom_eq hf ▸ z_dom)) =
      Classical.choose (fapply._proof_1 f (is_func_is_pfunc hf) z z_dom) := by
    congr
    funext w
    rw [propext_iff]
    constructor
    · rintro ⟨pair_z_w, unq_w⟩
      obtain ⟨_,_,_,l,eq⟩ := mem_prod.mp <| hf.left pair_z_w
      rcases pair_inj.mp eq with ⟨rfl, rfl⟩
      exact ⟨l, pair_z_w⟩
    · rintro ⟨_, pair_z_w⟩
      obtain ⟨a,pair_z_a,unq_a⟩ := hf.right z (is_func_dom_eq hf ▸ z_dom)
      exact ⟨pair_z_w, by intro w' pair_x_w'; rw [unq_a w' pair_x_w', unq_a w pair_z_w]⟩
  apply inj x y (Classical.choose <| hf.right x x_A) x_A y_A
  · exact choose_eq x_dom ▸ fapply_mem_range (is_func_is_pfunc hf) x_dom
  · exact pair_x_ε
  · rw [choose_eq x_dom, h, ← choose_eq y_dom]
    exact pair_y_ε

theorem IsPFunc.exists_unique_of_mem_dom {f A B : ZFSet}
  (hf : f.IsPFunc A B) {x : ZFSet} (hx : x ∈ f.Dom) :
    ∃! y, pair x y ∈ f := by
  unfold Dom at hx
  rw [mem_sep] at hx
  obtain ⟨xA, y, yB, xy_f⟩ := hx
  use y
  and_intros
  · exact xy_f
  · intro y' xy'_f
    symm
    exact hf.2 _ _ xy_f _ xy'_f

theorem fapply.of_pair {f A B : ZFSet} (hf : f.IsPFunc A B) {x y : ZFSet} (hxy : x.pair y ∈ f) :
  @ᶻf ⟨x, mem_dom hf hxy⟩ = ⟨y, And.right <| pair_mem_prod.mp <| hf.1 hxy⟩ := by
  dsimp [fapply]
  generalize_proofs y_def choose_B yB
  congr
  have spec := Classical.choose_spec y_def |>.2
  obtain ⟨w, xw, uniq⟩ := IsPFunc.exists_unique_of_mem_dom hf (mem_dom hf hxy)
  exact uniq _ hxy ▸ uniq _ spec

theorem IsPFunc.supset_of_range {f A B : ZFSet} (hf : f.IsPFunc A B) : f.Range ⊆ B := by
  intro y y_B
  rw [mem_sep] at y_B
  exact y_B.1

theorem IsPFunc.mem_range_of_mem {f A B : ZFSet}
  (hf : f.IsPFunc A B) {x y : ZFSet} (hxy : x.pair y ∈ f) :
    y ∈ f.Range := by
  rw [mem_sep]
  and_intros
  · obtain ⟨_,_,_,_,eq⟩ := mem_prod.mp <| hf.1 hxy
    rw [pair_inj] at eq
    rcases eq with ⟨rfl, rfl⟩
    assumption
  · exists x
    and_intros
    · exact mem_dom hf hxy
    · exact hxy

theorem IsPFunc.nonempty_range_of_nonempty_dom {f A B x y : ZFSet}
  (hf : f.IsPFunc A B) (hxy : x.pair y ∈ f) :
    f.Range ≠ ∅ := by
  have x_dom := mem_dom hf hxy
  have y_dom := mem_range_of_mem hf hxy
  rw [nonempty_exists_iff]
  exists y

theorem IsInjective.apply_inj_pfun {f A B : ZFSet}
  (hf : IsPFunc f A B) (inj : f.IsInjective (is_func_of_pfunc f hf)) :
    Function.Injective @ᶻf := by
  rintro ⟨x, x_dom⟩ ⟨y, y_dom⟩ h
  congr
  unfold IsInjective at inj
  apply inj x y (@ᶻf ⟨x, x_dom⟩) x_dom y_dom
  · dsimp [fapply]
    have : ∃ z ∈ B, pair x z ∈ f := by
      unfold Dom at x_dom
      rw [mem_sep] at x_dom
      obtain ⟨xA, y, yB, xy_f⟩ := x_dom
      use y
    generalize_proofs
    obtain ⟨memB, -⟩ := Classical.choose_spec this
    exact memB
  · exact fapply.def hf x_dom
  · rw [h]
    exact fapply.def hf y_dom

theorem IsInjective.apply_surj {f A B : ZFSet} (hf : IsFunc A B f) (surj : f.IsSurjective) :
    Function.Surjective @ᶻf := by
  rintro ⟨y, yB⟩
  obtain ⟨x, -, pair⟩ := surj y yB
  have x_dom : x ∈ f.Dom := mem_dom (is_func_is_pfunc hf) pair
  exists ⟨x, x_dom⟩
  exact fapply.of_pair (is_func_is_pfunc hf) pair

theorem IsInjective.apply_surj_pfun {f A B : ZFSet}
  (hf : IsPFunc f A B) (surj : f.IsSurjective (is_func_of_pfunc f hf)) :
    Function.Surjective @ᶻf := by
  rintro ⟨y, yB⟩
  obtain ⟨x, -, pair⟩ := surj y yB
  have x_dom' : x ∈ f.Dom := mem_dom hf pair
  exists ⟨x, x_dom'⟩
  exact fapply.of_pair hf pair

theorem prod_sep_is_pfunc_mem {A B C D : ZFSet} (subAC : A ⊆ C) (subBD : B ⊆ D) :
    (A.prod B).powerset.sep (IsPFunc · A B) ∈ (C.prod D).powerset.powerset := by
  rw [mem_powerset]
  intro S hS
  rw [mem_sep] at hS
  rw [mem_powerset] at hS ⊢
  intro x hx
  obtain ⟨_,l,_,r,rfl⟩ := mem_prod.mp <| hS.left hx
  rw [pair_mem_prod]
  exact ⟨subAC l, subBD r⟩

def lambda (dom : ZFSet) (ran : ZFSet) (exp : ZFSet → ZFSet) : ZFSet :=
  (dom.prod ran).sep fun xy ↦ xy.π₂ = exp xy.π₁

-- NOTE: deprecated syntax, use `λᶻ : dom → ran | x ↦ exp x` instead
-- notation:60 "λᶻ" " : " dom:max " → " ran:max " := " exp:max => lambda dom ran exp

open Lean Parser Term in
section
declare_syntax_cat funz_binder
syntax (name := identZBinder) Term.ident : funz_binder
syntax (name := tupleZBinder) "(" funz_binder ", " funz_binder ")" : funz_binder

def funZBinder : Parser := categoryParser `funz_binder 0

def funZType : Parser :=
  ":" >> ppSpace >> termParser leadPrec >> ppSpace >>
    unicodeSymbol "→" "->" >> ppSpace >> termParser leadPrec

def funZAlts : Parser :=
  "|" >> ppSpace >> funZBinder >> ppSpace >> unicodeSymbol "↦" "=>" >> ppSpace >> termParser

def basicFunZ : Parser := leading_parser (withAnonymousAntiquot := false)
  ppGroup (ppSpace >> funZType) >> funZAlts

@[term_parser] def funZ := leading_parser:maxPrec
  ppAllowUngrouped >> unicodeSymbol "λᶻ" "funᶻ" >> basicFunZ

partial def interpZBinder (x_def : TSyntax `term) (e : TSyntax `term) :
  TSyntax `funz_binder → MacroM (TSyntax `term)
  | `(funz_binder| $x:ident) => `(term| letI $x := $x_def; $e)
  | `(funz_binder| ($x, $y)) => do
    let e₂ ← interpZBinder (← `(term| ZFSet.π₂ w)) e y
    let e₁ ← interpZBinder (← `(term| ZFSet.π₁ w)) e₂ x
    `(term| letI w := $x_def; $e₁)
  | _ => Macro.throwUnsupported

/--
Interpret the syntax `λᶻ : dom → ran | x ↦ exp x` as `lambda dom ran (fun x ↦ exp x)`.

*Thanks to Ghilain for this notation.*
-/
macro_rules
| `(term| λᶻ : $dom → $ran | $x ↦ $e) => do
  `(term| ZFSet.lambda $dom $ran fun a ↦ $(← interpZBinder (←`(term| a)) e x))
end

theorem lambda_spec {dom ran : ZFSet} {exp : ZFSet → ZFSet} {x : ZFSet} {y : ZFSet} :
  x.pair y ∈ (λᶻ : dom → ran | z ↦ exp z) ↔ x ∈ dom ∧ y ∈ ran ∧ y = exp x := by
  rw [lambda, mem_sep, pair_mem_prod, π₁_pair, π₂_pair, and_assoc]

theorem mem_lambda {dom ran : ZFSet} {exp : ZFSet → ZFSet} {z : ZFSet} :
    (z ∈ λᶻ : dom → ran | x ↦ exp x) ↔
    ∃ x y : ZFSet, z = x.pair y ∧ x ∈ dom ∧ y ∈ ran ∧ y = exp x where
  mp := by
    intro hz
    rw [lambda, mem_sep] at hz
    obtain ⟨hz, eq⟩ := hz
    rw [mem_prod] at hz
    obtain ⟨x, x_dom, y, y_ran, rfl⟩ := hz
    rw [π₁_pair, π₂_pair] at eq
    subst y
    exists x, exp x
  mpr := by
    rintro ⟨x, y, ⟨rfl, x_dom, y_ran, rfl⟩⟩
    rw [lambda, mem_sep, mem_prod]
    and_intros
    · exact ⟨x, x_dom, exp x, y_ran, rfl⟩
    · rw [π₁_pair, π₂_pair]

theorem lambda_ext_iff {d r : ZFSet} {f₁ f₂ : ZFSet → ZFSet} (hf₁ : ∀ {x}, x ∈ d → f₁ x ∈ r) :
    (λᶻ : d → r | x ↦ f₁ x) = (λᶻ : d → r | x ↦ f₂ x) ↔ ∀ z ∈ d, f₁ z = f₂ z where
  mp := by
    intro h z hz
    rw [ZFSet.ext_iff] at h
    specialize h (z.pair (f₁ z))
    rw [lambda_spec, lambda_spec, eq_self, and_true] at h
    exact h.mp ⟨hz, hf₁ hz⟩ |>.2.2
  mpr := by
    intro hext
    ext1 z
    constructor
    · intro hz
      rw [mem_lambda] at hz
      obtain ⟨x, y, ⟨rfl, x_d, y_r, rfl⟩⟩ := hz
      rw [lambda_spec]
      exact ⟨x_d, y_r, hext x x_d⟩
    · intro hz
      rw [mem_lambda] at hz
      obtain ⟨x, y, ⟨rfl, x_d, y_r, rfl⟩⟩ := hz
      rw [lambda_spec]
      exact ⟨x_d, y_r, hext x x_d |>.symm⟩

theorem lambda_ext_iff' {d₁ d₂ r₁ r₂ : ZFSet} {f₁ f₂ : ZFSet → ZFSet}
  (hf₁ : ∀ {x}, x ∈ d₁ → f₁ x ∈ r₁) (hf₂ : ∀ {x}, x ∈ d₂ → f₂ x ∈ r₂) :
    (λᶻ : d₁ → r₁ | x ↦ f₁ x) = (λᶻ : d₂ → r₂ | x ↦ f₂ x) ↔ d₁ = d₂ ∧ ∀ z ∈ d₁, f₁ z = f₂ z where
  mp h := by
    rw [ZFSet.ext_iff] at h
    and_intros
    · ext1 z
      constructor
      · intro z_d₁
        specialize h <| z.pair (f₁ z)
        rw [lambda_spec, lambda_spec, eq_self, and_true] at h
        exact h.mp ⟨z_d₁, hf₁ z_d₁⟩ |>.1
      · intro z_d₂
        specialize h <| z.pair (f₂ z)
        rw [lambda_spec, lambda_spec, eq_self, and_true] at h
        exact h.mpr ⟨z_d₂, hf₂ z_d₂⟩ |>.1
    · intro z z_d₁
      specialize h <| z.pair (f₁ z)
      rw [lambda_spec, lambda_spec, eq_self, and_true] at h
      exact h.mp ⟨z_d₁, hf₁ z_d₁⟩ |>.2.2
  mpr := by
    rintro ⟨rfl, hext⟩
    ext1 z
    unfold lambda
    simp only [mem_sep, mem_prod]
    constructor
    · rintro ⟨⟨a, ha, b, hb, rfl⟩, eq⟩
      rw [π₁_pair, π₂_pair] at eq
      subst b
      and_intros
      · use a, ha, f₁ a
        and_intros
        · rw [hext a ha]
          exact hf₂ ha
        · rfl
      · rw [π₁_pair, π₂_pair, hext a ha]
    · rintro ⟨⟨a, ha, b, hb, rfl⟩, eq⟩
      rw [π₁_pair, π₂_pair] at eq
      subst b
      and_intros
      · use a, ha, f₂ a
        and_intros
        · rw [←hext a ha]
          exact hf₁ ha
        · rfl
      · rw [π₁_pair, π₂_pair, ←hext a ha]

open Classical in
theorem lambda_eta {A B : ZFSet} {f : ZFSet} (hf : A.IsFunc B f) :
  f = (λᶻ : A → B
          | x ↦ if hx : x ∈ A then @ᶻf ⟨x, by rwa [is_func_dom_eq hf]⟩ else ∅)
    := by
  ext1 z
  constructor <;> intro hz
  · obtain ⟨x, hx, y, hy, rfl⟩ := hf.1 hz |> mem_prod.mp
    rw [lambda_spec, dite_cond_eq_true (eq_true hx)]
    refine ⟨hx, hy, ?_⟩
    rw [fapply.of_pair (is_func_is_pfunc hf) hz]
  · rw [mem_lambda] at hz
    obtain ⟨x, y, rfl, xA, -, rfl⟩ := hz
    rw [dite_cond_eq_true (eq_true xA)]
    apply fapply.def

theorem lambda_subset {A B : ZFSet} {exp : ZFSet → ZFSet} : lambda A B exp ⊆ A.prod B := by
  intro z hz
  rw [lambda, mem_sep] at hz
  exact hz.1

theorem lambda_isFunc {A B : ZFSet} {f : ZFSet → ZFSet} (hf : ∀ {x}, x ∈ A → f x ∈ B) :
    A.IsFunc B (lambda A B f) := by
  and_intros
  · exact lambda_subset
  · intro x x_A
    exists f x
    and_intros
    · beta_reduce
      rw [lambda_spec]
      exact ⟨x_A, hf x_A, rfl⟩
    · beta_reduce
      intro y hy
      rw [lambda_spec] at hy
      exact hy.2.2

theorem mem_funs_of_lambda {A B : ZFSet} {f : ZFSet → ZFSet} (hf : ∀ {x}, x ∈ A → f x ∈ B) :
  lambda A B f ∈ A.funs B := mem_funs.mpr <| lambda_isFunc hf

theorem fapply_lambda {A B : ZFSet} {f : ZFSet → ZFSet}
  (hf : ∀ {x}, x ∈ A → f x ∈ B) {a : ZFSet} (ha : a ∈ A) :
    fapply (λᶻ : A → B | x ↦ f x) (is_func_is_pfunc <| lambda_isFunc hf)
      ⟨a, by rwa [is_func_dom_eq (lambda_isFunc hf)]⟩ = f a := by
  rw [fapply]
  generalize_proofs choose_y y_mem_B
  have y_def := Classical.choose_spec choose_y |>.2
  rw [lambda_spec] at y_def
  exact y_def.2.2

/--
The inverse of an injection is a function.
-/
@[zfun]
theorem inv_is_func_of_injective {f A B : ZFSet} {f_is_func : A.IsFunc B f}
  (hf : f.IsInjective f_is_func) :
    (f.Range).IsFunc A f⁻¹ := by
  and_intros
  · intro y hy
    rw [inv, mem_sep] at hy
    obtain ⟨y_mem, pair_f⟩ := hy
    rw [mem_prod] at y_mem
    obtain ⟨b, hb, a, ha, rfl⟩ := y_mem
    rw [π₁_pair, π₂_pair] at pair_f
    dsimp at pair_f
    rw [pair_mem_prod]
    and_intros
    · rw [mem_sep]
      and_intros
      · exact hb
      · use a
        and_intros
        · rwa [is_func_dom_eq f_is_func]
        · exact pair_f
    · exact ha
  · intro y hy
    rw [mem_sep] at hy
    obtain ⟨hy, x, hx, pair_f⟩ := hy
    use x
    have x_A : x ∈ A := by
      rw [mem_sep] at hx
      obtain ⟨xA, _, _, _⟩ := hx
      exact xA
    and_intros <;> beta_reduce
    · unfold inv
      rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair]
      exact ⟨⟨hy, x_A⟩, pair_f⟩
    · intro z hz
      rw [inv, mem_sep, π₁_pair, π₂_pair, pair_mem_prod] at hz
      symm
      exact hf x z y x_A hz.1.2 hy pair_f hz.2

-- macro_rules | `(tactic| zfun) => `(tactic| apply inv_is_func_of_injective; zfun)

/--
The inverse of a bijection is a function.
-/
@[zfun]
theorem inv_is_func_of_bijective {f A B : ZFSet} {f_is_func : A.IsFunc B f}
  (hf : f.IsBijective f_is_func) :
    B.IsFunc A (f.inv ) := by
  and_intros
  · intro xy hxy
    dsimp [inv] at hxy
    rw [mem_sep] at hxy
    obtain ⟨xy_prod, pair_f⟩ := hxy
    rw [mem_prod] at xy_prod
    obtain ⟨a, ha, b, hb, rfl⟩ := xy_prod
    rw [pair_mem_prod]
    exact ⟨ha, hb⟩
  · intro z hz
    rw [bijective_exists1_iff] at hf
    obtain ⟨x, ⟨x_A, hx⟩, x_unq⟩ := hf z hz
    simp_rw [mem_inv]
    use x
    and_intros <;> beta_reduce
    · exact hx
    · intro y hy
      apply x_unq y
      refine And.intro ?_ hy
      exact f_is_func.1 hy |> pair_mem_prod.mp |>.1

-- macro_rules | `(tactic| zfun) => `(tactic| apply inv_is_func_of_bijective; zfun)

/--
The inverse of a bijection is a bijection.
-/
theorem inv_bijective_of_bijective {f A B : ZFSet} {f_is_func : A.IsFunc B f}
  (hf : f.IsBijective f_is_func) :
    f⁻¹.IsBijective := by
  and_intros
  · intro x y z xB yB zA fxz fyz
    rw [mem_inv] at fxz fyz
    obtain ⟨_, _, unq⟩ := f_is_func.2 z zA
    rw [unq x fxz, unq y fyz]
  · intro x xA
    obtain ⟨y, yA, _⟩ := f_is_func.2 x xA
    use y
    and_intros
    · exact f_is_func.1 yA |> pair_mem_prod.mp |>.2
    · rw [mem_inv]
      exact yA

theorem composition_self_inv_of_bijective {f A B : ZFSet} {f_is_func : A.IsFunc B f}
  (hf : f.IsBijective) :
    f⁻¹ ∘ᶻ f = 𝟙A := by
  ext1 z
  constructor
  · intro hz
    rw [mem_composition] at hz
    obtain ⟨a, b, c, rfl, aA, cA, bB, ab_f, bc_finv⟩ := hz
    rw [mem_inv] at bc_finv
    rw [pair_mem_Id_iff aA]
    exact hf.1 _ _ _ aA cA bB ab_f bc_finv
  · intro hz
    rw [mem_Id_iff] at hz
    obtain ⟨a, aA, rfl⟩ := hz
    obtain ⟨b, ab_f, -⟩ := f_is_func.2 a aA
    simp only [mem_composition, pair_inj, existsAndEq, and_true, exists_and_left, exists_eq_left',
      and_self_left]
    apply And.intro aA
    use b, f_is_func.1 ab_f |> pair_mem_prod.mp |>.2
    rw [mem_inv, and_self]
    exact ab_f

theorem composition_inv_self_of_bijective {f A B : ZFSet} {f_is_func : A.IsFunc B f}
  (hf : f.IsBijective) :
    (f ∘ᶻ f⁻¹) = 𝟙B := by
  set g := f⁻¹
  have : B.IsFunc A g := inv_is_func_of_bijective hf
  have ginv_eq : g⁻¹ = f := inv_involutive _
  conv =>
    enter [1,1]
    rw [←ginv_eq]
  exact composition_self_inv_of_bijective <| inv_bijective_of_bijective hf

/--
The image of a set under a relation.
-/
def Image (R : ZFSet) {A B : ZFSet} (X : ZFSet) (hR : R ⊆ A.prod B := by zrel) : ZFSet :=
  B.sep (fun y ↦ ∃ x ∈ X, x.pair y ∈ R)

notation:60 R:max"[" X "]" => Image R X

theorem mem_Image {R A B X y : ZFSet} (hR : R ⊆ A.prod B) :
    y ∈ R[X] ↔ y ∈ B ∧ ∃ x ∈ X, x.pair y ∈ R where
  mp := by
    intro hy
    rw [Image, mem_sep] at hy
    exact ⟨hy.1, hy.2⟩
  mpr := by
    rintro ⟨yB, x, xX, xyR⟩
    rw [Image, mem_sep]
    exact ⟨yB, ⟨x, xX, xyR⟩⟩

@[simp]
theorem Image_empty {R A B : ZFSet} (hR : R ⊆ A.prod B) : R[∅] = ∅ := by
  ext1 y
  simp only [mem_Image, notMem_empty, false_and, exists_const, and_false]

theorem Image_of_singleton_pair_mem_iff {A B : ZFSet} {f : ZFSet}
  (hf : A.IsFunc B f) {a b : ZFSet} :
    a.pair b ∈ f ↔ f[{a}] = {b} := by
  constructor <;> intro h
  · ext1 z
    simp only [mem_Image, mem_singleton, exists_eq_left]
    constructor
    · rintro ⟨zB, hz⟩
      apply hf.2 a (hf.1 h |> pair_mem_prod.mp |>.1) |>.unique
      · exact hz
      · exact h
    · rintro rfl
      exact ⟨hf.1 h |> pair_mem_prod.mp |>.2, h⟩
  · rw [ZFSet.ext_iff] at h
    specialize h b
    rw [ZFSet.mem_singleton, eq_self, iff_true, mem_Image] at h
    simp only [mem_singleton, exists_eq_left] at h
    exact h.2

theorem eq_singleton_of_bijective_inv_Image_of_singleton {A B : ZFSet} {f : ZFSet}
  {hf : A.IsFunc B f} (hbij : f.IsBijective) {b : ZFSet} (hb : b ∈ B) :
    ∃ a ∈ A, f⁻¹[{b}] = {a} := by
  obtain ⟨a, aA, fab⟩ := hbij.2 b hb
  use a, aA
  rwa [←Image_of_singleton_pair_mem_iff (inv_is_func_of_bijective hbij), mem_inv]

theorem Image_singleton_eq_fapply {A B : ZFSet} {f : ZFSet}
  (hf : A.IsFunc B f) {a : ZFSet} (ha : a ∈ A) :
    f[{a}] = { (@ᶻf ⟨a, by rwa [is_func_dom_eq hf]⟩).val } := by
  rw [←Image_of_singleton_pair_mem_iff hf]
  apply fapply.def

theorem fapply_eq_Image_singleton {A B : ZFSet} {f : ZFSet}
  (hf : A.IsFunc B f) {a : ZFSet} (ha : a ∈ A) :
    @ᶻf ⟨a, by rwa [is_func_dom_eq hf]⟩ = ⋂₀ (f[{a}]) := by
  rw [Image_singleton_eq_fapply hf ha, sInter_singleton]

theorem fapply_composition {g f : ZFSet} {A B C : ZFSet}
  (hg : B.IsFunc C g) (hf : A.IsFunc B f) {x : ZFSet} (xA : x ∈ A) :
  @ᶻ(g ∘ᶻ f) ⟨x, by rwa [is_func_dom_eq]⟩ =
    @ᶻg ⟨@ᶻf ⟨x, by rwa [is_func_dom_eq]⟩,
      by rw [is_func_dom_eq]; apply fapply_mem_range⟩ := by
  unfold fcomp
  rw [Subtype.ext_iff]
  rw [fapply_eq_Image_singleton (IsFunc_of_composition_IsFunc hg hf) xA,
    fapply_eq_Image_singleton hg (fapply_mem_range _ _)]
  congr 1
  ext1 c
  constructor
  · intro hc
    simp only [mem_Image, mem_singleton, mem_composition, pair_inj, existsAndEq, and_true,
      exists_and_left, exists_eq_left', exists_eq_left] at hc
    obtain ⟨cC, -, -, b, bB, xb_f, bc_g⟩ := hc
    rw [fapply.of_pair (is_func_is_pfunc hf) xb_f, Image_singleton_eq_fapply hg bB, mem_singleton,
      fapply.of_pair (is_func_is_pfunc hg) bc_g]
  · intro hc
    rw [mem_Image] at hc
    obtain ⟨cC, b, hb, bc_g⟩ := hc
    rw [mem_singleton] at hb
    simp only [mem_Image, mem_singleton, mem_composition, pair_inj, existsAndEq, and_true,
      exists_and_left, exists_eq_left', exists_eq_left]
    and_intros
    · exact cC
    · exact xA
    · exact cC
    · use b
      subst hb
      and_intros
      · apply fapply_mem_range
      · apply fapply.def
      · exact bc_g

@[simp]
theorem Image_of_composition_inv_self_of_bijective {f A B : ZFSet} {f_is_func : A.IsFunc B f}
  (hf : f.IsBijective) {X : ZFSet} (hX : X ⊆ A) :
    f⁻¹[f[X]] = X := by
  ext1 x
  constructor
  · intro hx
    rw [mem_Image] at hx
    obtain ⟨xA, y, yfX, xy_finv⟩ := hx
    rw [mem_inv] at xy_finv
    rw [mem_Image] at yfX
    obtain ⟨yB, z, zX, zy_f⟩ := yfX
    obtain rfl := hf.1 x z y xA (f_is_func.1 zy_f |> pair_mem_prod.mp |>.1) yB xy_finv zy_f
    exact zX
  · intro hx
    rw [mem_Image]
    and_intros
    · exact hX hx
    · use @ᶻf ⟨x, by rw [is_func_dom_eq f_is_func]; exact hX hx⟩
      and_intros
      · rw [mem_Image]
        and_intros
        · apply fapply_mem_range
        · use x, hx
          apply fapply.def
      · rw [mem_inv]
        apply fapply.def

@[simp]
theorem Image_of_composition_self_inv_of_bijective {f A B : ZFSet} {f_is_func : A.IsFunc B f}
  (hf : f.IsBijective f_is_func) {X : ZFSet} (hX : X ⊆ B) :
    f[f⁻¹[X]] = X := by
  have := Image_of_composition_inv_self_of_bijective (f := f⁻¹) (inv_bijective_of_bijective hf) hX
  conv at this =>
    enter [1,1]
    rw [inv_involutive]
  exact this

end Functions

section Finite
/--
A set is finite if it is equinumerous to a (ZF) natural number, i.e.
if there is a bijection between the set and a natural number.
-/
def IsFinite (x : ZFSet) := ∃ (n f : ZFSet) (_ : n ∈ Nat)
  (hf : f ∈ x.funs n), f.IsInjective (mem_funs.mp hf)

abbrev ZFFinSet := {x : ZFSet // x.IsFinite}

noncomputable def Max (S : ZFSet) [linord : LinearOrder {x // x ∈ S}] : ZFSet :=
  ε (S.sep fun x ↦ (_ : x ∈ S) → ∀ y, (_ : y ∈ S) → linord.le ⟨y, ‹_›⟩ ⟨x, ‹_›⟩)
noncomputable def Min (S : ZFSet) [linord : LinearOrder {x // x ∈ S}] : ZFSet :=
  ε (S.sep fun x ↦ (_ : x ∈ S) → ∀ y, (_ : y ∈ S) → linord.le ⟨x, ‹_›⟩ ⟨y, ‹_›⟩)

def LinearOrder.ofSubset {S T : ZFSet} (S_T : S ⊆ T) [linordT : LinearOrder {x // x ∈ T}] :
    LinearOrder {x // x ∈ S} :=
  LinearOrder.lift'
    (fun ⟨x, hx⟩ => (⟨x, S_T hx⟩:{x // x ∈ T})) (by rintro ⟨x, hx⟩ ⟨y, hy⟩ _; injections; congr)

example {x : ZFSet} {hx : x ∈ Nat} :
  @ZFSet.Max ({x} : ZFSet)
    (@LinearOrder.ofSubset ({x} : ZFSet) Nat
      (by intro; rw [mem_singleton]; rintro rfl; exact hx) ZFNat.instLinearOrder) = x := by
  unfold Max
  simp_rw [mem_singleton, mem_sep, mem_singleton]
  have :
    ∃ z, z = x ∧ ∀ (x_1 : z = x) (y : ZFSet) (x_2 : y = x),
      (⟨y, by rwa [x_2]⟩ : ZFNat) ≤ ⟨z, by rwa [x_1]⟩ := by
    exists x
    and_intros
    · rfl
    · rintro _ y rfl
      apply le_refl
  exact Classical.epsilon_spec this |>.left

/- NOTE:
The following is now unprovable: `∃ x, ZFSet.Max Nat = x`
-/

/-
-- Is this even true?
example {x : ZFSet} : x.IsFinite ↔ Finite (x.toSet) := by
-/

theorem Min_exists {S : ZFFinSet} [linord : LinearOrder {x // x ∈ S.val}] (nempS : S.val.Nonempty) :
  ∃ (x : {x // x ∈ S.val}), ∀ y, (y_S : y ∈ S.val) → linord.le x ⟨y, ‹_›⟩ := by
  -- obtain ⟨n, f, n_Nat, hf, inj⟩ := IsFinite.exist_bij S.property
  by_contra! contr
  admit

theorem Min_mem (S : ZFFinSet) [linord : LinearOrder {x // x ∈ S.val}] (nempS : S.val.Nonempty) :
    S.val.Min ∈ S.val := by
  admit

theorem Min_spec {S : ZFFinSet} [linord : LinearOrder {x // x ∈ S.val}] (nempS : S.val.Nonempty) :
  ∀ (y : {x // x ∈ S.val}), linord.le ⟨S.val.Min, Min_mem S nempS⟩ y := by
  obtain ⟨n, f, n_Nat, hf, inj⟩ := S.property
  by_contra! contr
  admit

theorem Max_exists {S : ZFFinSet} [linord : LinearOrder {x // x ∈ S.val}] (nempS : S.val.Nonempty) :
  ∃ (x : {x // x ∈ S.val}), ∀ y, y ≤ x := by
  obtain ⟨n, f, n_Nat, hf, inj⟩ := S.property
  by_contra! contr
  admit

theorem Max_mem (S : ZFFinSet) [linord : LinearOrder {x // x ∈ S.val}] (nempS : S.val.Nonempty) :
    S.val.Max ∈ S.val := by
  admit

theorem Max_spec {S : ZFFinSet} [linord : LinearOrder {x // x ∈ S.val}] (nempS : S.val.Nonempty) :
  ∀ (y : {x // x ∈ S.val}), linord.le ⟨S.val.Max, Max_mem S nempS⟩ y := by
  obtain ⟨n, f, n_Nat, hf, inj⟩ := S.property
  by_contra! contr
  admit

end Finite

section Auxiliary

@[simp]
noncomputable def get (x : ZFSet) (n : ℕ) (i : Fin n) : ZFSet :=
  match n, i with
  | 1, i => x
  | n+2, i => if h : i = Fin.last (n+1) then x.π₂ else get x.π₁ (n+1) (i.castPred h)

open Classical in
def hasArity (x : ZFSet) (n : ℕ) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | n+1 =>
    if ∃ a b, x = ZFSet.pair a b then hasArity x.π₁ n
    else False

theorem isTuple_pair {a b : ZFSet} : hasArity (ZFSet.pair a b) 2 := by
  rw [hasArity]
  · split_ifs with cond
    · trivial
    · push_neg at cond
      nomatch cond a b
  · rintro ⟨⟩

theorem sep_mem_powerset {D T : ZFSet} {P : ZFSet → Prop} :
    D ∈ T.powerset → D.sep P ∈ T.powerset := by
  intro hD
  rw [mem_powerset, subset_def] at hD ⊢
  exact fun _ hz => hD (ZFSet.mem_sep.mp hz).1

theorem subset_of_𝔹_sInter (B : ZFSet) : B ⊆ ZFSet.𝔹 → (⋂₀ B : ZFSet) ∈ ZFSet.𝔹 := by
  intro h
  simp_rw [← ZFSet.mem_powerset, ZFSet.ZFBool.powerset_𝔹_def,
    ZFSet.mem_insert_iff, ZFSet.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · rw [ZFSet.sInter_empty]
    exact ZFSet.ZFBool.zffalse_mem_𝔹
  · rw [ZFSet.sInter_singleton]
    exact ZFSet.ZFBool.zffalse_mem_𝔹
  · rw [ZFSet.sInter_singleton]
    exact ZFSet.ZFBool.zftrue_mem_𝔹
  · rw [ZFSet.sInter_pair, ZFSet.ZFBool.mem_𝔹_iff]
    left
    ext1 x
    constructor
    · intro hx
      rcases ZFSet.mem_inter.mp hx
      assumption
    · intro hx
      unfold ZFSet.zffalse at hx
      nomatch (ZFSet.notMem_empty x) hx

theorem subset_of_𝔹_sUnion (B : ZFSet) : B ⊆ ZFSet.𝔹 → (⋃₀ B : ZFSet) ∈ ZFSet.𝔹 := by
  intro h
  simp_rw [← ZFSet.mem_powerset, ZFSet.ZFBool.powerset_𝔹_def,
    ZFSet.mem_insert_iff, ZFSet.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · rw [ZFSet.sUnion_empty]
    exact ZFSet.ZFBool.zffalse_mem_𝔹
  · rw [ZFSet.sUnion_singleton]
    exact ZFSet.ZFBool.zffalse_mem_𝔹
  · rw [ZFSet.sUnion_singleton]
    exact ZFSet.ZFBool.zftrue_mem_𝔹
  · rw [ZFSet.sUnion_pair, ZFSet.ZFBool.mem_𝔹_iff]
    right
    ext1 x
    constructor
    · intro hx
      rcases ZFSet.mem_union.mp hx with hx | hx
      · nomatch (ZFSet.notMem_empty x) hx
      · exact hx
    · intro hx
      exact mem_union.mpr <| Or.inr hx

theorem sInter_sep_subset_of_𝔹_mem_𝔹 {D : ZFSet} {P : ZFSet → Prop} :
    D ⊆ ZFSet.𝔹 → (⋂₀ (D.sep P) : ZFSet) ∈ ZFSet.𝔹 := by
  intro h
  apply ZFSet.subset_of_𝔹_sInter (ZFSet.sep P D)
  intros _ hx
  rw [ZFSet.mem_sep] at hx
  exact h hx.1

theorem sUnion_sep_subset_of_𝔹_mem_𝔹 {D : ZFSet} {P : ZFSet → Prop} :
    D ⊆ ZFSet.𝔹 → (⋃₀ (D.sep P) : ZFSet) ∈ ZFSet.𝔹 := by
  intro h
  apply ZFSet.subset_of_𝔹_sUnion (ZFSet.sep P D)
  intros _ hx
  rw [ZFSet.mem_sep] at hx
  exact h hx.1

theorem IsFunc.sep_on_eq {A B : ZFSet} {f : ZFSet → ZFSet} (hf : ∀ x ∈ A, f x ∈ B) :
    IsFunc A B <| (A.prod B).sep (fun z ↦ ∃ x y : ZFSet, z = x.pair y ∧ y = f z.π₁) := by
  unfold IsFunc
  and_intros
  · exact sep_subset_self
  · intro x hx
    exists f x
    and_intros
    · beta_reduce
      rw [mem_sep, pair_mem_prod]
      and_intros
      · exact hx
      · exact hf x hx
      · exists x, (f x)
        and_intros
        · rfl
        · rw [π₁_pair]
    · intro w hw
      rw [mem_sep, pair_mem_prod] at hw
      obtain ⟨⟨hx, hw⟩, z, _, eq, rfl⟩ := hw
      rw [π₁_pair] at eq
      obtain ⟨rfl, rfl⟩ := pair_inj.mp eq
      rfl

theorem IsFunc.is_func_on_range {f A B : ZFSet} (hf : A.IsFunc B f) :
  A.IsFunc (f.Range) f := by
    conv =>
      arg 1
      rw [←is_func_dom_eq hf]
    exact is_func_dom_range f (is_func_is_pfunc hf)

theorem IsPFunc.empty_dom {f A B : ZFSet} (hf : IsPFunc f A B) (dom_emp : f.Dom = ∅) : f = ∅ := by
  ext1 z
  constructor
  · intro hz
    obtain ⟨x, xA, y, yB, rfl⟩ := mem_prod.mp <| hf.1 hz
    nomatch notMem_empty _ <| dom_emp ▸ mem_dom hf hz
  · intro hz
    nomatch notMem_empty _ <| hz

theorem IsPFunc.empty_range_of_empty_dom {f A B : ZFSet}
  (hf : IsPFunc f A B) (dom_emp : f.Dom = ∅) : f.Range = ∅ := by
    unfold Range
    conv =>
      arg 1
      rw [dom_emp, empty_dom hf dom_emp]
    simp only [notMem_empty, and_self, exists_const, sep_empty_iff,
      not_false_eq_true, implies_true, or_true]

theorem IsPFunc.exists_dom_of_mem_range {f A B : ZFSet}
  (hf : IsPFunc f A B) {y : ZFSet} (hy : y ∈ f.Range) :
    ∃ x ∈ A, pair x y ∈ f := by
  unfold Range at hy
  rw [mem_sep] at hy
  obtain ⟨y_B, x, x_dom, pair⟩ := hy
  exists x
  and_intros
  · unfold Dom at x_dom
    rw [mem_sep] at x_dom
    exact x_dom.1
  · exact pair

theorem IsFunc.surj_on_range {f A B : ZFSet} (hf : IsFunc A B f) :
    IsSurjective (f := f) (A := A) (B := f.Range) (is_func_on_range hf) := by
  intro y hy
  exact IsPFunc.exists_dom_of_mem_range (is_func_is_pfunc hf) hy

theorem bijective_of_injective {f A B : ZFSet} (hf : IsFunc A B f) (inj : f.IsInjective hf) :
    f.IsBijective (A := A) (B := Range f) (IsFunc.is_func_on_range hf) := by
  constructor
  · intro x y z xA yA zRange xz yz
    apply inj x y z xA yA _ xz yz
    rw [mem_sep] at zRange
    exact zRange.1
  · intro y hy
    exact IsPFunc.exists_dom_of_mem_range (is_func_is_pfunc hf) hy

theorem IsFunc.range_eq_of_surjective {f A B : ZFSet} (hf : IsFunc A B f)
  (surj : f.IsSurjective hf) :
    f.Range = B := by
  ext1 y
  constructor
  · intro hy
    exact (mem_sep.mp hy).1
  · intro hy
    rw [mem_sep]
    and_intros
    · exact hy
    · obtain ⟨x, x_dom, xy⟩ := surj y hy
      exists x
      and_intros
      · exact ZFSet.mem_dom (is_func_is_pfunc hf) xy
      · exact xy

attribute [-instance] SetLike.instPartialOrder

instance instPreorder_mem_Nat {n : ZFSet} (hn : n ∈ Nat) : Preorder {x // x ∈ n} where
  le := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦
    (⟨a, ZFNat.mem_Nat_of_mem_mem_Nat hn ha⟩ : ZFNat) ≤
    (⟨b, ZFNat.mem_Nat_of_mem_mem_Nat hn hb⟩ : ZFNat)
  le_trans _ _ _ := ZFNat.le_trans
  le_refl _ := ZFNat.instPreorder.le_refl _
  lt_iff_le_not_ge := fun _ _ => Eq.to_iff rfl

theorem IsFinite.empty : (∅:ZFSet).IsFinite := by
  unfold IsFinite IsInjective
  simp only [notMem_empty, IsEmpty.forall_iff, implies_true, mem_funs, exists_prop, and_true,
    exists_and_left, IsFunc, prod_empty_left]
  exact ⟨∅, ZFNat.zero_in_Nat, ∅, fun _ => id⟩

theorem IsFinite.subset {A B : ZFSet} (finB : B.IsFinite) (subAB : A ⊆ B) :
  A.IsFinite := by
  obtain ⟨n, f, hn, hf, inj⟩ := finB
  generalize_proofs f_func at inj
  exists n, A.prod n |>.sep fun z => ∃ x y : ZFSet, z ∈ f ∧ z = x.pair y, hn, ?_
  · rw [mem_funs] at hf ⊢
    and_intros
    · intro z hz
      rw [mem_sep] at hz
      exact hz.1
    · intro x xA
      simp only [exists_and_left, mem_sep, mem_prod, pair_inj,
        exists_eq_right_right', exists_eq', and_true]
      obtain ⟨z, hz, z_unq⟩ := hf.2 x (subAB xA)
      exists z
      and_intros
      · exact xA
      · exact And.right <| pair_mem_prod.mp <| hf.1 hz
      · exact hz
      · intro y hy
        apply z_unq
        exact hy.2
  · generalize_proofs f'_A_n
    intro x y z xA yA zn eq
    simp_rw [mem_sep, pair_mem_prod, pair_inj] at eq ⊢
    intro ⟨_, _, _, yz, rfl, rfl⟩
    obtain ⟨_, _, xz, rfl, rfl⟩ := eq.2
    exact inj x y z (subAB xA) (subAB yA) zn xz yz

theorem IsFinite.insert {A : ZFSet} (finA : A.IsFinite) (x : ZFSet) :
  (insert x A).IsFinite := by
  by_cases hx : x ∈ A
  · have : Insert.insert x A = A := by
      ext1 w
      rw [mem_insert_iff]
      constructor
      · rintro (rfl | h) <;> assumption
      · intro; right; assumption
    rwa [this]
  · obtain ⟨n, f, hn, hf, inj⟩ := finA
    let sucn := ZFNat.succ (⟨n, hn⟩:ZFNat)
    exists sucn, f ∪ {x.pair n}, Subtype.property _, ?_
    · rw [mem_funs]
      and_intros
      · intro z hz
        rw [mem_union, mem_singleton] at hz
        rcases hz with hz | rfl
        · obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.mp <| mem_funs.mp hf |>.1 hz
          simp_rw [mem_prod, mem_insert_iff]
          exists a
          and_intros
          · right; exact ha
          · exists b
            and_intros
            · unfold sucn ZFNat.succ
              rw [mem_insert_iff]
              right
              exact hb
            · rfl
        · rw [pair_mem_prod]
          and_intros
          · exact mem_insert x A
          · unfold sucn ZFNat.succ
            rw [mem_insert_iff]
            left
            rfl
      · intro z hz
        rw [mem_insert_iff] at hz
        rcases hz with rfl | hz
        · exists n
          beta_reduce
          and_intros
          · rw [mem_union, mem_singleton]
            right
            rfl
          · intro z' hz'
            rw [mem_union, mem_singleton] at hz'
            rcases hz' with hz' | hz'
            · nomatch hx <| And.left <| pair_mem_prod.mp <| mem_funs.mp hf |>.1 hz'
            · rw [pair_inj] at hz'
              exact hz'.2
        · obtain ⟨w, hw, w_unq⟩ := mem_funs.mp hf |>.2 z hz
          exists w
          beta_reduce
          and_intros
          · rw [mem_union]
            left
            exact hw
          · intro w' hw'
            rw [mem_union, mem_singleton, pair_inj] at hw'
            rcases hw' with hw' | ⟨rfl, rfl⟩
            · exact w_unq w' hw'
            · contradiction
    · intro w y z wA yA zn wz yz
      rw [mem_insert_iff] at wA yA
      unfold sucn ZFNat.succ at zn
      rw [mem_insert_iff] at zn
      simp_rw [mem_union, mem_singleton, pair_inj] at zn wz yz
      rcases wz with wz | ⟨rfl, rfl⟩ <;>
      rcases yz with yz | ⟨rfl, ⟨⟩⟩
      · exact inj w y z
          (And.left <| pair_mem_prod.mp <| mem_funs.mp hf |>.1 wz)
          (And.left <| pair_mem_prod.mp <| mem_funs.mp hf |>.1 yz)
          (And.right <| pair_mem_prod.mp <| mem_funs.mp hf |>.1 yz) wz yz
      · nomatch mem_irrefl _ (And.right <| pair_mem_prod.mp <| mem_funs.mp hf |>.1 wz)
      · nomatch mem_irrefl _ (And.right <| pair_mem_prod.mp <| mem_funs.mp hf |>.1 yz)
      · rfl

theorem IsFinite.disjoint_union {A B : ZFSet}
  (finA : A.IsFinite) (finB : B.IsFinite) (disjoint : A ∩ B = ∅) :
    (A ∪ B).IsFinite := by
  obtain ⟨n₁, fA, hn₁, hfA, injA⟩ := finA
  by_cases A_emp : A = ∅
  · subst A
    rwa [empty_union]
  · have n₁_ne_zero : n₁ ≠ ∅ := by
      rintro rfl
      obtain ⟨a, ha⟩ := nonempty_exists_iff.mp A_emp
      obtain ⟨b, hb, -⟩ := mem_funs.mp hfA |>.2 a ha
      nomatch notMem_empty _ <| And.right <| pair_mem_prod.mp <| mem_funs.mp hfA |>.1 hb
    obtain ⟨n₂, fB, hn₂, hfB, injB⟩ := finB
    let f' :=
      fA ∪ (B.prod (⟨n₁, hn₁⟩ + ⟨n₂, hn₂⟩ : ZFNat)).sep fun z ↦
        ∃ (x y : ZFSet) (hy : y ∈ Nat), z = x.pair (⟨y, hy⟩ + ⟨n₁, hn₁⟩ : ZFNat) ∧ x.pair y ∈ fB
    exists ((⟨n₁, hn₁⟩ : ZFNat) + (⟨n₂, hn₂⟩ : ZFNat)), f', ?_, ?_
    · apply Subtype.property
    · rw [mem_funs]
      and_intros
      · intro z hz
        rcases mem_union.mp hz with hz | hz
        · obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.mp <| mem_funs.mp hfA |>.1 hz
          rw [pair_mem_prod, mem_union]
          and_intros
          · left; exact ha
          · have b_mem_Nat : b ∈ Nat := ZFNat.mem_Nat_of_mem_mem_Nat hn₁ hb
            change (⟨b, b_mem_Nat⟩ : ZFNat) < ⟨n₁, hn₁⟩ at hb
            change (⟨b, b_mem_Nat⟩ : ZFNat) < ⟨n₁, hn₁⟩ + ⟨n₂, hn₂⟩
            rw [←@ZFNat.add_zero ⟨b, b_mem_Nat⟩]
            exact ZFNat.add_lt_add_of_lt_of_le hb ZFNat.zero_le
        · rw [mem_sep, mem_prod] at hz
          obtain ⟨⟨z₁,hz₁,z₂,hz₂, rfl⟩, _, b, hb, eq, z₁b⟩ := hz
          obtain ⟨rfl, rfl⟩ := pair_inj.mp eq
          rw [pair_mem_prod, mem_union]
          and_intros
          · right; exact hz₁
          · exact hz₂
      · intro z hz
        rw [mem_union] at hz
        rcases hz with hz | hz
        · obtain ⟨a, z_a_fA, a_unq⟩ := mem_funs.mp hfA |>.2 z hz
          exists a
          beta_reduce
          and_intros
          · unfold f'
            rw [mem_union]
            left
            exact z_a_fA
          · intro y hy
            rw [mem_union] at hy
            rcases hy with hy | hy
            · exact a_unq y hy
            · simp_rw [mem_sep, pair_mem_prod, pair_inj] at hy
              obtain ⟨⟨hz, hy⟩, _, b, hb, eq, z_b⟩ := hy
              have zB := And.left <| pair_mem_prod.mp <| mem_funs.mp hfB |>.1 z_b
              have contr := ZFSet.ext_iff.mp disjoint z
              simp_rw [mem_inter, notMem_empty, iff_false] at contr
              nomatch contr ⟨‹z ∈ A›, hz⟩
        · obtain ⟨a, z_a_fB, a_unq⟩ := mem_funs.mp hfB |>.2 z hz
          have a_Nat : a ∈ Nat :=
            ZFNat.mem_Nat_of_mem_mem_Nat hn₂ <|
              And.right <| pair_mem_prod.mp <| mem_funs.mp hfB |>.1 z_a_fB
          exists (⟨a, a_Nat⟩ + ⟨n₁, hn₁⟩ : ZFNat)
          beta_reduce
          and_intros
          · unfold f'
            rw [mem_union, mem_sep, pair_mem_prod]
            right
            and_intros
            · exact hz
            · change (⟨a, a_Nat⟩ + ⟨n₁, hn₁⟩ : ZFNat) < ⟨n₁, hn₁⟩ + ⟨n₂, hn₂⟩
              rw [add_comm, ZFNat.add_lt_add_iff_left]
              exact And.right <| pair_mem_prod.mp <| mem_funs.mp hfB |>.1 z_a_fB
            · exists z, a, a_Nat
          · intro y hy
            rw [mem_union] at hy
            rcases hy with hy | hy
            · have zA := And.left <| pair_mem_prod.mp <| mem_funs.mp hfA |>.1 hy
              have contr := ZFSet.ext_iff.mp disjoint z
              simp_rw [mem_inter, notMem_empty, iff_false] at contr
              nomatch contr ⟨zA, hz⟩
            · simp only [exists_and_right, mem_sep, mem_prod, pair_inj,
                exists_eq_right_right', exists_and_left] at hy
              obtain ⟨⟨zB, z_lt_n₂⟩, _, w, ⟨rfl, w_Nat, rfl⟩, zw⟩ := hy
              obtain ⟨⟩ := a_unq w zw
              rfl
    · intro x y z xA yA hz xz yz
      have contr := ZFSet.ext_iff.mp disjoint
      simp_rw [mem_inter, notMem_empty, iff_false] at contr
      rw [mem_union] at xA yA
      rcases xA with xA | xB <;>
      rcases yA with yA | yB <;>
      unfold f' at xz yz <;>
      rw [mem_union] at xz yz <;>
      rcases xz with xz | xz <;>
      rcases yz with yz | yz
      · obtain ⟨⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 xz
        obtain ⟨⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 yz
        apply injA <;> assumption
      · simp_rw [mem_sep, pair_mem_prod, pair_inj, exists_and_right, exists_and_left] at yz
        obtain ⟨_, w, ⟨rfl, ⟨w_Nat, rfl⟩⟩, yw⟩ := yz.2
        nomatch contr y ⟨yA, And.left <| pair_mem_prod.mp <| mem_funs.mp hfB |>.1 yw⟩
      · simp_rw [mem_sep, pair_mem_prod, pair_inj, exists_and_right, exists_and_left] at xz
        obtain ⟨_, w, ⟨rfl, ⟨w_Nat, rfl⟩⟩, xw⟩ := xz.2
        nomatch contr x ⟨xA, And.left <| pair_mem_prod.mp <| mem_funs.mp hfB |>.1 xw⟩
      · simp only [exists_and_right, mem_sep, mem_prod, pair_inj,
          exists_eq_right_right', exists_and_left] at xz
        nomatch contr x ⟨xA, xz.1.1⟩
      · obtain ⟨⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 xz
        obtain ⟨⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 yz
        apply injA <;> assumption
      · simp only [exists_and_right, mem_sep, mem_prod, pair_inj,
          exists_eq_right_right', exists_and_left] at yz
        obtain ⟨⟨-, w_lt_n₂⟩, ⟨_, v, ⟨rfl, v_Nat, rfl⟩, yv⟩⟩ := yz
        have v_add_n₁_lt_n₁ := And.right <| pair_mem_prod.mp <| mem_funs.mp hfA |>.1 xz
        change (⟨v, v_Nat⟩ + ⟨n₁, hn₁⟩ : ZFNat) < ⟨n₁, hn₁⟩ at v_add_n₁_lt_n₁
        conv at v_add_n₁_lt_n₁ =>
          rhs
          rw [←@ZFNat.zero_add ⟨n₁, hn₁⟩]
        rw [ZFNat.add_lt_add_iff_right] at v_add_n₁_lt_n₁
        nomatch ZFNat.not_lt_zero v_add_n₁_lt_n₁
      · nomatch contr y ⟨And.left <| pair_mem_prod.mp <| mem_funs.mp hfA |>.1 yz, yB⟩
      · simp only [exists_and_right, mem_sep, mem_prod, pair_inj,
          exists_eq_right_right', exists_and_left] at xz
        nomatch contr x ⟨xA, xz.1.1⟩
      · obtain ⟨⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 xz
        obtain ⟨⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 yz
        apply injA <;> assumption
      · obtain ⟨zA, -⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 xz
        nomatch contr x ⟨And.left <| pair_mem_prod.mp <| mem_funs.mp hfA |>.1 xz, xB⟩
      · simp only [exists_and_right, mem_sep, mem_prod, pair_inj,
          exists_eq_right_right', exists_and_left] at xz
        obtain ⟨⟨-, w_lt_n₂⟩, ⟨_, v, ⟨rfl, v_Nat, rfl⟩, yv⟩⟩ := xz
        have v_add_n₁_lt_n₁ := And.right <| pair_mem_prod.mp <| mem_funs.mp hfA |>.1 yz
        change (⟨v, v_Nat⟩ + ⟨n₁, hn₁⟩ : ZFNat) < ⟨n₁, hn₁⟩ at v_add_n₁_lt_n₁
        conv at v_add_n₁_lt_n₁ =>
          rhs
          rw [←@ZFNat.zero_add ⟨n₁, hn₁⟩]
        rw [ZFNat.add_lt_add_iff_right] at v_add_n₁_lt_n₁
        nomatch ZFNat.not_lt_zero v_add_n₁_lt_n₁
      · simp only [exists_and_right, mem_sep, mem_prod, pair_inj,
          exists_eq_right_right', exists_and_left] at yz
        nomatch contr y ⟨yA, yz.1.1⟩
      · obtain ⟨⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 xz
        obtain ⟨⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 yz
        apply injA <;> assumption
      · obtain ⟨xA, -⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 xz
        nomatch contr x ⟨xA, xB⟩
      · obtain ⟨yA, -⟩ := pair_mem_prod.mp <| mem_funs.mp hfA |>.1 yz
        nomatch contr y ⟨yA, yB⟩
      · simp only [exists_and_right, mem_sep, mem_prod, pair_inj,
          exists_eq_right_right', exists_and_left] at xz yz
        obtain ⟨⟨-, w_lt_n₂⟩, ⟨_, w, ⟨rfl, w_Nat, rfl⟩, xw⟩⟩ := xz
        obtain ⟨⟨_, w_lt_n₁⟩, ⟨_, v, ⟨rfl, v_Nat, eq⟩, yv⟩⟩ := yz
        rw [←Subtype.ext_iff, ZFNat.add_right_cancel] at eq
        injection eq
        subst w
        exact injB x y v xB yB (And.right <| pair_mem_prod.mp <| mem_funs.mp hfB |>.1 xw) xw yv

theorem IsFinite.union {A B : ZFSet} (finA : A.IsFinite) (finB : B.IsFinite) :
  (A ∪ B).IsFinite := by
  have : A ∪ B = (A \ B) ∪ B := by
    ext1 z
    simp_rw [mem_union, mem_diff]
    constructor
    · rintro (hA | hB)
      · by_cases hB : z ∈ B
        · right; exact hB
        · left; exact ⟨hA, hB⟩
      · right; exact hB
    · rintro (⟨hA, -⟩ | hB)
      · left; exact hA
      · right; exact hB
  rw [this]
  have : (A \ B) ∩ B = ∅ := by
    ext1 z
    rw [mem_inter, mem_diff, and_assoc]
    simp only [not_and_self, and_false, notMem_empty]
  apply IsFinite.disjoint_union (IsFinite.subset finA ?_) finB this
  intro z hz
  rw [mem_diff] at hz
  exact hz.1

theorem IsFinite.inter {A B : ZFSet} (fin : A.IsFinite ∨ B.IsFinite) :
  (A ∩ B).IsFinite := by
  wlog fin : A.IsFinite
  · replace fin := Or.resolve_left ‹_ ∨ _› fin
    rw [inter_comm]
    exact this (Or.inl fin) fin
  · apply IsFinite.subset fin
    · intro z hz
      rw [mem_inter] at hz
      exact hz.1

theorem IsFinite.diff {A B : ZFSet} (finA : A.IsFinite) :
  (A \ B).IsFinite := by
  apply IsFinite.subset finA
  intro z hz
  rw [mem_diff] at hz
  exact hz.1

@[induction_eliminator]
def ZFFinSet.inductionOn {P : ZFFinSet → Prop}
  (empty : P ⟨∅, IsFinite.empty⟩)
  (insert : ∀ (S : ZFFinSet) (x : ZFSet), P S → x ∉ S.val → P ⟨insert x S, S.property.insert x⟩) :
  ∀ (S : ZFFinSet), P S := by
  intro ⟨S, finS⟩
  obtain ⟨n , fS , hn, hfS, fS_inj⟩ := finS
  generalize_proofs finS
  generalize_proofs fS_is_func at fS_inj
  revert S fS
  apply ZFNat.ind n hn
  · intro S fS h _ _ _
    rw [mem_funs, IsFunc, prod_empty_right] at h
    obtain ⟨⟩ := subset_of_empty h.1
    have : S = ∅ := by
      simp only [subset_refl, notMem_empty, existsUnique_false, imp_false, true_and] at h
      exact (eq_empty S).mpr h
    subst S
    exact empty
  · intro n hn IH S fS _ S_fin fS_fun fS_inj
    by_cases n_range : n ∈ fS.Range
    · rw [Range, mem_sep, mem_insert_iff, eq_self, true_or, true_and,] at n_range
      obtain ⟨a, a_dom, an⟩ := n_range
      let S' := S \ {a}
      let fS' := fS \ {a.pair n}
      have S'_fin : S'.IsFinite := IsFinite.diff S_fin
      have S'_is_func : S'.IsFunc n fS' := by
        and_intros
        · intro z hz
          unfold fS' at hz
          rw [mem_diff, mem_singleton] at hz
          obtain ⟨x, xS, y, yS, rfl⟩ := mem_prod.mp <| fS_fun.1 hz.1
          rw [pair_inj] at hz
          rw [pair_mem_prod]
          rw [mem_insert_iff] at yS
          rcases yS with rfl | yS
          · obtain ⟨⟩ :=
              fS_inj a x y (And.left <| pair_mem_prod.mp <| fS_fun.1 an) xS (mem_insert y y) an hz.1
            nomatch hz.2 (pair_inj.mp rfl)
          · and_intros
            · unfold S'
              rw [mem_diff, mem_singleton]
              and_intros
              · exact xS
              · rintro rfl
                rw [not_and, eq_self, true_implies] at hz
                obtain ⟨fS_x, hfS_x, fS_x_unq⟩ := fS_fun.2 x xS
                obtain ⟨⟩ := fS_x_unq y hz.1
                obtain ⟨⟩ := fS_x_unq n an
                nomatch mem_irrefl _ yS
            · exact yS
        · intro z zS
          rw [mem_diff, mem_singleton] at zS
          obtain ⟨w, hw, w_unq⟩ := fS_fun.2 z zS.1
          exists w
          and_intros
          · unfold fS'
            beta_reduce
            rw [mem_diff, mem_singleton, pair_inj]
            and_intros
            · exact hw
            · rw [not_and_or]
              left
              exact zS.2
          · intro w' hw'
            unfold fS' at hw'
            rw [mem_diff, mem_singleton, pair_inj] at hw'
            exact w_unq w' hw'.left
      have : fS'.IsInjective := by
        intro x y z xS' yS' zn xy yz
        apply fS_inj x y z
        · exact mem_diff.mp xS' |>.1
        · exact mem_diff.mp yS' |>.1
        · exact mem_insert_of_mem n zn
        all_goals
          unfold fS' at xy
          rw [mem_diff, mem_singleton] at xy yz
        · exact xy.1
        · exact yz.1
      specialize IH S' fS' (mem_funs.mpr S'_is_func) S'_fin S'_is_func this
      have : S = Insert.insert a S' := by classical
        unfold S'
        ext1 z
        simp_rw [mem_insert_iff, mem_diff, mem_singleton, or_and_left, Classical.em, and_true]
        constructor
        · exact Or.inr
        · rintro (rfl | hz)
          · exact And.left <| pair_mem_prod.mp <| fS_fun |>.1 an
          · exact hz
      specialize insert _ a IH (by
        unfold S'
        rw [mem_diff, mem_singleton, not_and_or, not_not]
        right; rfl)
      conv at insert =>
        enter [1,1]
        rw [←this]
      exact insert
    · have : S.IsFunc n fS := by
        and_intros
        · intro z hz
          obtain ⟨a, aS, b, bS, rfl⟩ := mem_prod.mp <| fS_fun.1 hz
          rw [mem_insert_iff] at bS
          rw [pair_mem_prod]
          apply And.intro aS
          rcases bS with rfl | bS
          · unfold Range at n_range
            simp_rw [mem_sep, mem_insert_iff, true_or, true_and, not_exists, not_and] at n_range
            nomatch n_range a ⟨aS, b, Or.inl rfl, hz⟩ hz
          · exact bS
        · exact fS_fun.2
      apply IH S fS (mem_funs.mpr this) S_fin this
      intro x y z xS yS zn xy yz
      apply fS_inj x y z xS yS
      · rw [mem_insert_iff]
        right
        exact zn
      · exact xy
      · exact yz

theorem IsFinite.singleton {x : ZFSet} : ({x} : ZFSet).IsFinite := by
  exists (1:ZFNat), {x.pair (0:ZFNat)}, ?_, ?_
  · exact SetLike.coe_mem 1
  · rw [mem_funs]
    and_intros
    · intro z hz
      rw [mem_singleton] at hz
      obtain ⟨⟩ := hz
      rw [pair_mem_prod, mem_singleton, eq_self, true_and]
      exact singleton_subset_mem_iff.mp fun _ => id
    · intro z
      simp only [mem_singleton, pair_inj]
      rintro rfl
      simp only [true_and, existsUnique_eq]
  · intro x y z
    simp only [mem_singleton, pair_inj, and_imp]
    intros
    subst_eqs
    rfl

theorem IsFinite.prod_singleton {A x : ZFSet} (finA : A.IsFinite) :
  (A.prod {x}).IsFinite := by
  induction hA : (⟨A, finA⟩ : ZFFinSet) using ZFFinSet.inductionOn generalizing A finA x with
  | empty =>
    injections
    subst_vars
    rwa [prod_empty_left]
  | insert E e ih he =>
    injections
    subst_vars
    rw [insert_prod]
    apply IsFinite.union
    · apply ih
      rfl
    · have : ({e} : ZFSet).prod {x} = {e.pair x} := by
        ext1 z
        simp only [mem_prod, mem_singleton, exists_eq_left]
      rw [this]
      apply IsFinite.singleton

theorem IsFinite.singleton_prod {A x : ZFSet} (finA : A.IsFinite) :
  (({x} : ZFSet).prod A).IsFinite := by
  induction hA : (⟨A, finA⟩ : ZFFinSet) using ZFFinSet.inductionOn generalizing A finA x with
  | empty =>
    injections
    subst_vars
    rwa [prod_empty_right]
  | insert E e ih he =>
    injections
    subst_vars
    rw [prod_insert]
    apply IsFinite.union
    · apply ih
      rfl
    · have : ({x} : ZFSet).prod {e} = {x.pair e} := by
        ext1 z
        simp only [mem_prod, mem_singleton, exists_eq_left]
      rw [this]
      apply IsFinite.singleton

theorem IsFinite.prod {A B : ZFSet} (finA : A.IsFinite) (finB : B.IsFinite) :
  (A.prod B).IsFinite := by
  induction hA : (⟨A, finA⟩ : ZFFinSet) using ZFFinSet.inductionOn generalizing A finA with
  | empty =>
    injections
    subst_vars
    rwa [prod_empty_left]
  | insert S x ih x_not_mem_S =>
    injections
    subst_vars
    rw [insert_prod]
    apply IsFinite.union
    · apply ih
      rfl
    · exact singleton_prod finB

theorem IsFinite.sep {A : ZFSet} (finA : A.IsFinite) (P : ZFSet → Prop) : (A.sep P).IsFinite :=
  subset finA sep_subset_self

theorem ZFNat.every_nat_isfinite (n : ZFNat) : n.val.IsFinite :=
  ⟨n, 𝟙n, n.property, mem_funs.mpr <| Id.IsFunc, Id.IsBijective.1⟩

theorem IsFinite.exists_bij {A : ZFSet} (finA : A.IsFinite) :
  ∃ (n : ZFSet) (f : ZFSet) (_ : n ∈ Nat) (hf : f ∈ A.funs n), f.IsBijective (mem_funs.mp hf) := by
  induction hA : (⟨A, finA⟩ : ZFFinSet) using ZFFinSet.inductionOn generalizing A finA with
  | empty =>
    injections
    subst_vars
    exists (0 : ZFNat), ∅, ?_, ?_
    · exact SetLike.coe_mem 0
    · simp_rw [mem_funs, IsFunc, prod_empty_left, subset_refl, notMem_empty,
        existsUnique_false, imp_self, implies_true, and_self]
    · and_intros
      · intro _ _ _ h
        nomatch notMem_empty _ h
      · intro _ h
        nomatch notMem_empty _ h
  | insert S x ih x_not_mem_S =>
    injections
    subst_vars
    obtain ⟨n, f, hn, hf, bij⟩ :=
      ih (IsFinite.subset (A := S) finA (fun _ ↦ mem_insert_of_mem x)) rfl
    exists (ZFNat.succ ⟨n, hn⟩), f ∪ {x.pair n}, ?_, ?_
    · exact SetLike.coe_mem (ZFNat.succ ⟨n, hn⟩)
    · rw [mem_funs]
      and_intros
      · intro z hz
        rw [mem_union, mem_singleton] at hz
        rcases hz with hz | rfl
        · obtain ⟨a, aS, b, bS, rfl⟩ := mem_prod.mp <| (mem_funs.mp hf).1 hz
          simp only [mem_prod, mem_insert_iff, pair_inj, exists_eq_right_right']
          obtain ⟨aS, bn⟩ := pair_mem_prod.mp <| (mem_funs.mp hf).1 hz
          and_intros
          · right
            exact aS
          · change ⟨b, ZFNat.mem_Nat_of_mem_mem_Nat hn bS⟩ < ZFNat.succ ⟨n, hn⟩
            trans ⟨n, hn⟩
            · exact bn
            · exact ZFNat.lt_succ
        · rw [pair_mem_prod, mem_insert_iff]
          and_intros
          · left
            rfl
          · exact ZFNat.lt_succ
      · simp only [mem_insert_iff, mem_union, mem_singleton, pair_inj, forall_eq_or_imp, true_and]
        and_intros
        · exists n
          and_intros
          · right; rfl
          · intro w hw
            rcases hw with hw | rfl
            · nomatch x_not_mem_S (And.left <| pair_mem_prod.mp <| (mem_funs.mp hf).1 hw)
            · rfl
        · intro a aS
          obtain ⟨w, wS, w_unq⟩ := (mem_funs.mp hf).2 a aS
          exists w
          and_intros
          · left; exact wS
          · intro w' hw'
            rcases hw' with hw' | ⟨rfl, rfl⟩
            · obtain ⟨⟩ := w_unq w' hw'
              rfl
            · contradiction
    · rw [bijective_exists1_iff] at bij ⊢
      intro y hy
      have y_Nat := ZFNat.mem_Nat_of_mem_mem_Nat (SetLike.coe_mem (ZFNat.succ ⟨n, hn⟩)) hy
      change (⟨y, y_Nat⟩ : ZFNat) < ZFNat.succ ⟨n, hn⟩ at hy
      rw [← ZFNat.lt_le_iff] at hy
      rcases hy with hy | hy
      · obtain ⟨x, ⟨xS, xy⟩, x_unq⟩ := bij y hy
        exists x
        and_intros
        · rw [mem_insert_iff]
          right; exact xS
        · rw [mem_union, mem_singleton]
          left; exact xy
        · intro x' hx'
          rw [mem_insert_iff, mem_union, mem_singleton, pair_inj] at hx'
          rcases hx' with ⟨rfl|_, _|⟨_,rfl⟩⟩
          · nomatch x_not_mem_S <| And.left <| pair_mem_prod.mp <| (mem_funs.mp hf).1 ‹_ ∈ f›
          · nomatch mem_irrefl _ <| And.right <| pair_mem_prod.mp <| (mem_funs.mp hf).1 ‹_ ∈ f›
          · obtain ⟨⟩ := x_unq x' ⟨‹_›, ‹_›⟩
            rfl
          · subst_vars
            contradiction
      · injection hy
        subst y
        exists x
        and_intros
        · rw [mem_insert_iff]
          left; rfl
        · rw [mem_union, mem_singleton]
          right; rfl
        · intro y hy
          simp only [mem_insert_iff, mem_union, mem_singleton, pair_inj, and_true] at hy
          rcases hy with ⟨rfl|_, _|_⟩
          · rfl
          · rfl
          · nomatch mem_irrefl _ <| And.right <| pair_mem_prod.mp <| (mem_funs.mp hf).1 ‹_ ∈ f›
          · assumption

open Classical in
noncomputable def Card : ZFFinSet → ZFNat := fun ⟨S, Sfin⟩ =>
  if S = ∅ then 0 else
  have ex_bij := (IsFinite.exists_bij Sfin)
  ⟨choose ex_bij, choose <| choose_spec <| choose_spec ex_bij⟩

@[simp]
theorem Card.empty_iff {S : ZFFinSet} : Card S = 0 ↔ S = ⟨∅, IsFinite.empty⟩ := by
  constructor
  · intro h
    rw [Card] at h
    split_ifs at h with Semp
    · exact Subtype.ext Semp
    · replace Semp : S.val ≠ ∅ := Semp
      obtain ⟨s, hs⟩ := (@nonempty_exists_iff S).mp Semp
      extract_lets ex_bij at h
      let n := Classical.choose ex_bij
      obtain ⟨f, hn, hf, bij⟩ := Classical.choose_spec ex_bij
      refold_let n at *
      have : n = ∅ := by
        rwa [ZFNat.nat_zero_eq, ←Subtype.val_inj] at h
      rw [this, mem_funs, IsFunc] at hf
      obtain ⟨w, hw, w_unq⟩ := hf.2 s hs
      nomatch notMem_empty _ <| And.right <| pair_mem_prod.mp <| hf.1 hw
  · rintro ⟨⟩
    rw [Card, eq_self, if_true]

@[simp]
theorem Card.empty : Card ⟨∅, IsFinite.empty⟩ = 0 := empty_iff.mpr rfl

@[simp]
theorem Card.singleton (x : ZFSet) : Card ⟨{x}, IsFinite.singleton⟩ = 1 := by
  rw [Card]
  split_ifs with h
  · simp_rw [eq_empty, mem_singleton] at h
    nomatch h x
  · extract_lets ex_bij
    let n := Classical.choose ex_bij
    generalize_proofs _ hn
    obtain ⟨f, hn, hf, bij⟩ := Classical.choose_spec ex_bij
    refold_let n at *
    have : (⟨n, hn⟩ : ZFNat) = 1 := by
      simp_rw [mem_funs, IsFunc, mem_singleton, forall_eq] at hf
      obtain ⟨k, hk, k_unq⟩ := hf.2
      have := And.right <| pair_mem_prod.mp <| hf.1 hk
      induction ind_n : (⟨n, hn⟩ : ZFNat) using ZFNat.induction generalizing n hn with
      | zero =>
        injection ind_n with eq
        rw [eq] at this
        nomatch notMem_empty _ this
      | succ m IH =>
        injection ind_n with eq
        rw [eq, mem_insert_iff] at this
        rcases this with rfl | this
        · rw [←@ZFNat.zero_add 1, ←ZFNat.add_one_eq_succ,
            ZFNat.add_right_cancel, ZFNat.nat_zero_eq, Subtype.ext_iff]
          dsimp
          symm
          apply k_unq
          obtain ⟨x', hx'⟩ := bij.2 ∅ <| eq ▸ ZFNat.zero_lt_succ
          obtain ⟨⟩ := mem_singleton.mp hx'.1
          exact hx'.2
        · obtain ⟨w, hw, xm⟩ := bij.2 m (eq ▸ mem_insert m m)
          obtain ⟨⟩ := mem_singleton.mp hw
          rw [k_unq m xm] at this
          nomatch mem_irrefl _ this
    exact this

theorem Card.insert {S : ZFFinSet} {x : ZFSet} (hx : x ∉ S.val) :
  Card ⟨insert x S.val, S.property.insert x⟩ = Card S + 1 := by
  induction S with
  | empty =>
      rw [Card.empty, zero_add]
      simp only [insert_empty_eq, singleton]
  | insert S s IH hs =>
    admit

def Card.inductionOn {P : ZFFinSet → Prop}
  (zero : P ⟨∅, IsFinite.empty⟩)
  (succ : ∀ n : ZFNat,
    (∀ (S : ZFFinSet), n = Card S → P S) → ∀ (S' : ZFFinSet), Card S' = n + 1 → P S') :
    ∀ (S : ZFFinSet), P S := by
  intro ⟨S, hS⟩
  admit

theorem IsFinite.powerset {A : ZFSet} (finA : A.IsFinite) : A.powerset.IsFinite := by
  induction hA : (⟨A, finA⟩ : ZFFinSet) using Card.inductionOn generalizing A finA with
  | zero =>
    injections
    subst_vars
    rw [ZFBool.powerset_false]
    exact singleton
  | succ n IH S cardS =>
    rw [Subtype.ext_iff] at hA
    dsimp at hA
    subst A
    by_cases hS : S.val = ∅
    · rw [hS, ZFBool.powerset_false]
      exact singleton
    · obtain ⟨s, hs⟩ := (@nonempty_exists_iff S).mp hS
      specialize IH ⟨S \ ({s} : ZFSet), IsFinite.diff finA⟩
      have : S.val = Insert.insert s (S.val \ ({s} : ZFSet)) := by
        ext
        simp only [mem_insert_iff, mem_diff, mem_singleton, or_and_left,
          Classical.em, and_true, iff_or_self]
        rintro rfl
        assumption
      change Card ⟨S.val, S.property⟩ = n + 1 at cardS
      have : S = ⟨
        Insert.insert s (S.val \ ({s} : ZFSet)),
        IsFinite.subset finA <| subset_of_subset_of_eq (fun _ => id) this.symm⟩ :=
        Subtype.ext this
      rw [this] at cardS
      dsimp at cardS
      have := Card.insert (S := ⟨S.val \ ({s} : ZFSet), IsFinite.diff finA⟩) (x := s) (by
        rw [mem_diff, mem_singleton, not_and_or, not_not]
        right; rfl)
      rw [this, ZFNat.add_right_cancel] at cardS
      clear this
      specialize IH cardS.symm (IsFinite.diff finA)
      · exact ({s} : ZFSet)
      · admit

theorem IsFinite.finite_funs (S T : ZFSet) (finS : S.IsFinite) (finT : T.IsFinite) :
    (S.funs T).IsFinite :=
  sep (powerset (prod finS finT)) (S.IsFunc T)

theorem IsFinite.exists_bij_mono_iff {S : ZFSet} [inst : Preorder {x // x ∈ S}] :
    S.IsFinite ↔
    ∃ (n : ZFSet) (f : ZFSet) (_ : n ∈ Nat) (hf : f ∈ S.funs n),
      f.IsBijective (mem_funs.mp hf) ∧
      @IsStrictMono f S n inst (instPreorder_mem_Nat ‹_ ∈ Nat›) (mem_funs.mp hf) := by
  constructor
  · intro Sfin
    obtain ⟨n, f, hn, hf, bij⟩ := Sfin.exists_bij
    exists n
    admit
  · rintro ⟨n, f, hn, hf, bij, -⟩
    exists n, f, hn, hf
    exact bij.1


open Classical in
theorem Min_mem_of_non_empty_finite {S : ZFSet} [inst : LinearOrder {x // x ∈ S}]
  (S_nemp : S.Nonempty) (S_fin : S.IsFinite) :
  ZFSet.Min S ∈ S := by
  unfold ZFSet.Min
  beta_reduce
  simp only [mem_sep]
  apply epsilon_spec ?_
    (p := fun z ↦
      z ∈ S ∧ ∀ (x : z ∈ S) (y : ZFSet.{u_1}) (x_1 : y ∈ S), inst.le ⟨z, x⟩ ⟨y, x_1⟩) |>.1
  beta_reduce
  obtain ⟨n, f, hn, hf, bij, mono⟩ :=
    IsFinite.exists_bij_mono_iff (inst := inst.toPreorder).mp S_fin
  have : n ≠ (0 : ZFNat).1 := by
    suffices (⟨n, hn⟩ : ZFNat) ≠ (0 : ZFNat) by
      rintro rfl
      exact this rfl
    induction h : (⟨n, hn⟩ : ZFNat) using ZFNat.induction with
    | zero =>
      injections
      subst n
      rw [mem_funs, IsFunc, prod_empty_right] at hf
      have : f = ∅ := by
        ext1
        constructor
        · exact (hf.1 ·)
        · exact (False.elim <| notMem_empty _ ·)
      exfalso
      obtain ⟨x, hx⟩ := (nonempty_def _).mp S_nemp
      obtain ⟨y, hy, -⟩ := hf.2 x hx
      have := IsPFunc.mem_range_of_mem (is_func_is_pfunc (mem_funs.mp ‹f ∈ _›)) hy
      rw [IsFunc.range_eq_of_surjective (mem_funs.mp ‹f ∈ _›) bij.2] at this
      nomatch notMem_empty _ this
    | succ n _ => exact ZFNat.succ_ne_zero n
  rw [mem_funs] at hf
  have : (0 : ZFNat).1 ∈ f.Range := by
    rw [IsFunc.range_eq_of_surjective hf bij.2]
    suffices (0:ZFNat) < ⟨n, hn⟩ from this
    cases h : (⟨n, hn⟩:ZFNat) using ZFNat.cases with
    | zero =>
      injection h
      contradiction
    | succ => exact ZFNat.zero_lt_succ
  rw [mem_sep] at this
  obtain ⟨x₀, x₀_dom, x₀_def⟩ := this.2
  have x₀_S : x₀ ∈ S := by
    rw [mem_sep] at x₀_dom
    exact x₀_dom.1

  by_contra! contr
  specialize contr x₀ x₀_S
  obtain ⟨_, x₁, x₁_S, x₁_lt_x₀⟩ := contr
  obtain ⟨y₁, y₁_def, -⟩ := hf.2 x₁ x₁_S
  have := IsPFunc.mem_range_of_mem (is_func_is_pfunc hf) y₁_def
  rw [IsFunc.range_eq_of_surjective hf bij.2] at this

  unfold IsStrictMono at mono
  have : (⟨y₁, ZFNat.mem_Nat_of_mem_mem_Nat hn this⟩ : ZFNat) < 0 := by
    specialize mono x₁ x₀ y₁ (0:ZFNat) x₁_S this y₁_def x₀_S _ x₀_def _
    · suffices 0 < (⟨n, hn⟩ : ZFNat) from this
      cases h : (⟨n, hn⟩:ZFNat) using ZFNat.cases with
      | zero =>
        injection h
        contradiction
      | succ n => exact ZFNat.zero_lt_succ
    · exact x₁_lt_x₀
    · nomatch ZFNat.not_lt_zero <| not_le.mp mono.2
  exact ZFNat.not_lt_zero this

theorem image_of_lambda_subset_range {A B φ : ZFSet} {hφ : A.IsFunc B φ} {S : ZFSet} :
  φ[S] ⊆ B := by
  intro y hy
  rw [mem_Image] at hy
  obtain ⟨hy, x, hx, φxy⟩ := hy
  exact hφ.1 φxy |> pair_mem_prod.mp |>.2

open Classical in
noncomputable def fprod {A B A' B' : ZFSet} (f g : ZFSet)
  (hf : A.IsFunc A' f := by zfun) (hg : B.IsFunc B' g := by zfun) : ZFSet :=
  λᶻ : A.prod B → A'.prod B'
     |    z     ↦ if hz : z ∈ A.prod B then
                   let a := z.π₁
                   let b := z.π₂
                   let fa : ZFSet := @ᶻf ⟨a, by
                     rw [is_func_dom_eq hf]
                     rw [pair_eta hz, pair_mem_prod] at hz
                     exact hz.1⟩
                   let gb : ZFSet := @ᶻg ⟨b, by
                     rw [is_func_dom_eq hg]
                     rw [pair_eta hz, pair_mem_prod] at hz
                     exact hz.2⟩
                   fa.pair gb
                  else ∅
@[zfun]
theorem fprod_is_func {A B A' B' φ ψ : ZFSet} (hφ : A.IsFunc A' φ) (hψ : B.IsFunc B' ψ) :
  (A.prod B).IsFunc (A'.prod B') (fprod φ ψ) := by
  and_intros
  · intro z hz
    simp only [fprod, mem_prod, mem_lambda, existsAndEq, and_true] at hz
    obtain ⟨x, rfl, ⟨a, aA, b, bB, rfl⟩, a', ha', b', hb', eq⟩ := hz
    -- obtain ⟨a', b', a, b, rfl, ⟨aA, bB⟩, ⟨a'A', b'B'⟩, eq⟩ := hz
    rw [dite_cond_eq_true (eq_true (by rw [pair_mem_prod]; exact ⟨aA, bB⟩)), pair_inj] at eq
    obtain ⟨rfl, rfl⟩ := eq
    let φa : ZFSet := @ᶻφ ⟨a, by rwa [is_func_dom_eq hφ]⟩
    let ψb : ZFSet := @ᶻψ ⟨b, by rwa [is_func_dom_eq hψ]⟩

    simp only [mem_prod, pair_inj, exists_eq_right_right', π₁_pair, π₂_pair]
    and_intros
    · exact aA
    · exact bB
    · simp only [π₁_pair, π₂_pair] at ha' hb'
      use φa, ha', ψb, hb'
      rw [dite_cond_eq_true (eq_true (by rw [pair_mem_prod]; exact ⟨aA, bB⟩))]

  · intro z hz
    rw [mem_prod] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    let φa : ZFSet := @ᶻφ ⟨a, by rwa [is_func_dom_eq hφ]⟩
    let ψb : ZFSet := @ᶻψ ⟨b, by rwa [is_func_dom_eq hψ]⟩
    use φa.pair ψb
    and_intros <;> beta_reduce
    · simp_rw [fprod, lambda_spec, pair_mem_prod]
      rw [dite_cond_eq_true (eq_true (by rw [pair_mem_prod]; exact ⟨ha, hb⟩)), pair_inj]
      and_intros
      · exact ha
      · exact hb
      · apply fapply_mem_range
      · apply fapply_mem_range
      · simp only [π₁_pair]
        rfl
      · simp only [π₂_pair]
        rfl
    · intro y hy
      simp_rw [fprod, lambda_spec, pair_mem_prod, π₁_pair, π₂_pair] at hy
      rw [dite_cond_eq_true (eq_true (by rw [pair_mem_prod]; exact ⟨ha, hb⟩))] at hy
      exact hy.2.2

-- macro_rules | `(tactic| zfun) => `(tactic| apply fprod_is_func <;> zfun)

theorem fprod_bijective_of_bijective {A B A' B' φ ψ : ZFSet}
  {hφ : A.IsFunc A' φ} {hψ : B.IsFunc B' ψ}
  (φ_bij : φ.IsBijective) (ψ_bij : ψ.IsBijective) :
    (fprod φ ψ).IsBijective := by
  and_intros
  · intro x y z hx hy hz xy yz
    simp only [fprod, mem_prod, mem_lambda, pair_inj, existsAndEq, and_true,
      exists_eq_left'] at xy yz
    obtain ⟨⟨a, ha, b, hb, rfl⟩, -, rfl⟩ := xy
    obtain ⟨⟨c, hc, d, hd, rfl⟩, -, eq⟩ := yz
    rw [dite_cond_eq_true (eq_true (by rw [pair_mem_prod]; exact ⟨ha, hb⟩)),
        dite_cond_eq_true (eq_true (by rw [pair_mem_prod]; exact ⟨hc, hd⟩)), pair_inj] at eq
    simp only [π₁_pair, SetLike.coe_eq_coe, π₂_pair] at eq
    obtain ⟨φa_eq_φc, ψb_eq_ψd⟩ := eq
    rw [pair_inj]
    and_intros
    · obtain ⟨⟩ := IsInjective.apply_inj hφ φ_bij.1 φa_eq_φc
      rfl
    · obtain ⟨⟩ := IsInjective.apply_inj hψ ψ_bij.1 ψb_eq_ψd
      rfl
  · intro y hy
    rw [mem_prod] at hy
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    let φ_inv_a' : ZFSet := fapply φ⁻¹ (is_func_is_pfunc <| inv_is_func_of_bijective φ_bij)
      ⟨a', by rwa [is_func_dom_eq (inv_is_func_of_bijective φ_bij)]⟩
    let ψ_inv_b' : ZFSet := fapply ψ⁻¹ (is_func_is_pfunc <| inv_is_func_of_bijective ψ_bij)
      ⟨b', by rwa [is_func_dom_eq (inv_is_func_of_bijective ψ_bij)]⟩
    use φ_inv_a'.pair ψ_inv_b'
    and_intros
    · rw [pair_mem_prod]
      and_intros
      · apply fapply_mem_range
      · apply fapply_mem_range
    · simp only [fprod, mem_prod, lambda_spec, pair_inj, exists_eq_right_right', π₁_pair, π₂_pair]
      and_intros
      · apply fapply_mem_range
      · apply fapply_mem_range
      · exact ha'
      · exact hb'
      · rw [dite_cond_eq_true
          (eq_true (by rw [pair_mem_prod]; and_intros <;> apply fapply_mem_range)),
          pair_inj]
        and_intros
        · rw [←fapply_composition hφ (inv_is_func_of_bijective φ_bij) ha',
            fapply_eq_Image_singleton
              (IsFunc_of_composition_IsFunc hφ (inv_is_func_of_bijective φ_bij)) ha']
          conv =>
            enter [2, 1, 1]
            change φ ∘ᶻ φ⁻¹
            rw [composition_inv_self_of_bijective φ_bij]
          rw [←fapply_eq_Image_singleton Id.IsFunc ha', fapply_Id ha']
        · rw [←fapply_composition hψ (inv_is_func_of_bijective ψ_bij) hb',
            fapply_eq_Image_singleton
              (IsFunc_of_composition_IsFunc hψ (inv_is_func_of_bijective ψ_bij)) hb']
          conv =>
            enter [2, 1, 1]
            change ψ ∘ᶻ ψ⁻¹
            rw [composition_inv_self_of_bijective ψ_bij]
          rw [←fapply_eq_Image_singleton Id.IsFunc hb', fapply_Id hb']

theorem mem_fprod {A B C D f g x : ZFSet} {hf : A.IsFunc C f} {hg : B.IsFunc D g} :
  x ∈ fprod f g ↔ ∃ (a b : ZFSet) (ha : a ∈ A) (hb : b ∈ B),
    let fa : ZFSet := @ᶻf ⟨a, by rwa [is_func_dom_eq hf]⟩
    let gb : ZFSet := @ᶻg ⟨b, by rwa [is_func_dom_eq hg]⟩
    x = (a.pair b).pair (fa.pair gb) where
  mp := by
    intro hx
    rw [fprod, mem_lambda] at hx
    obtain ⟨ab, cd, rfl, hab, hcd, rfl⟩ := hx
    rw [dite_cond_eq_true (eq_true hab)] at hcd
    rw [mem_prod] at hab
    obtain ⟨a, ha, b, hb, rfl⟩ := hab
    rw [pair_mem_prod] at hab
    simp only [mem_prod, pair_inj, exists_eq_right_right', π₁_pair, π₂_pair,
      exists_and_left, existsAndEq, and_true, exists_eq_left']
    rw [dite_cond_eq_true (eq_true ‹_›)]
    simp only [exists_prop, and_true, ha, hb]
  mpr := by
    rintro ⟨a, b, ha, hb, rfl⟩
    simp only [fprod, mem_prod, mem_lambda, pair_inj, existsAndEq, and_true,
      exists_eq_right_right', SetLike.coe_mem, true_and, exists_eq_right', exists_eq_left', π₁_pair,
      π₂_pair, left_eq_dite_iff, not_and]
    and_intros
    · exact ha
    · exact hb
    · intro c
      nomatch c ha hb

theorem pair_mem_fprod {A B C D f g x y : ZFSet} {hf : A.IsFunc C f} {hg : B.IsFunc D g} :
  x.pair y ∈ fprod f g ↔ ∃ (a b : ZFSet) (ha : a ∈ A) (hb : b ∈ B),
    let fa : ZFSet := @ᶻf ⟨a, by rwa [is_func_dom_eq hf]⟩
    let gb : ZFSet := @ᶻg ⟨b, by rwa [is_func_dom_eq hg]⟩
    x = a.pair b ∧ y = fa.pair gb := by
  rw [mem_fprod]
  simp only [pair_inj, exists_and_left]

@[simp]
theorem fapply_fprod {A B C D f g a b : ZFSet} (hf : A.IsFunc C f) (hg : B.IsFunc D g)
  (ha : a ∈ A) (hb : b ∈ B) :
    @ᶻ(fprod f g)
      ⟨a.pair b, by rw [is_func_dom_eq (fprod_is_func hf hg), pair_mem_prod]; exact ⟨ha, hb⟩⟩ =
    let fa : ZFSet := @ᶻf ⟨a, by rwa [is_func_dom_eq hf]⟩
    let gb : ZFSet := @ᶻg ⟨b, by rwa [is_func_dom_eq hg]⟩
    fa.pair gb := by
  conv =>
    enter [1]
    rw [fapply_eq_Image_singleton (fprod_is_func hf hg) (by rw [pair_mem_prod]; exact ⟨ha, hb⟩)]
    dsimp [fprod]
    rw [
      ←fapply_eq_Image_singleton
        (lambda_isFunc
          (fun h ↦ by
            rw [dite_cond_eq_true (eq_true h), pair_mem_prod]
            and_intros <;> apply fapply_mem_range))
        (by rw [pair_mem_prod]; exact ⟨ha, hb⟩),
      fapply_lambda (fun h ↦ by
        rw [dite_cond_eq_true (eq_true h), pair_mem_prod]
        and_intros <;> apply fapply_mem_range)
        (by rw [pair_mem_prod]; exact ⟨ha, hb⟩),
      dite_cond_eq_true (eq_true (by rw [pair_mem_prod]; exact ⟨ha, hb⟩))]
    simp only [π₁_pair, π₂_pair]

open ZFSet Classical in
theorem composition_fprod_Image_bijective {A B A' B' φ ψ : ZFSet}
  {hφ : A.IsFunc A' φ} {hψ : B.IsFunc B' ψ}
  (φ_bij : φ.IsBijective) (ψ_bij : ψ.IsBijective) :
    let φ_ψ : ZFSet := fprod φ ψ
    have φ_ψ_bij : φ_ψ.IsBijective := fprod_bijective_of_bijective φ_bij ψ_bij

    let Φ : ZFSet := λᶻ : (A.prod B).powerset → (A'.prod B').powerset
                        |                   S ↦ φ_ψ[S]
    ∃ (hΦ : (A.prod B).powerset.IsFunc (A'.prod B').powerset Φ), IsBijective Φ hΦ := by
  extract_lets φ_ψ hφ_ψ φ_ψ_bij
  use ?_
  · and_intros
    · intro x y z hx hy hz x_z y_z
      rw [mem_lambda] at x_z y_z
      simp only [pair_inj, mem_powerset, existsAndEq, and_true, exists_eq_left'] at x_z y_z
      obtain ⟨_, _, rfl⟩ := x_z
      obtain ⟨_, _, eq⟩ := y_z
      rw [ZFSet.ext_iff] at eq
      simp only [mem_Image, mem_prod, and_congr_right_iff, forall_exists_index, and_imp] at eq
      ext1 z
      constructor <;> intro hz
      · obtain ⟨a, ha, b, hb, rfl⟩ := ‹x ⊆ A.prod B› hz |> mem_prod.mp
        letI φa : ZFSet := @ᶻφ ⟨a, by rwa [is_func_dom_eq hφ]⟩
        letI ψb : ZFSet := @ᶻψ ⟨b, by rwa [is_func_dom_eq hψ]⟩
        specialize eq (φa.pair ψb) φa (fapply_mem_range _ _) ψb (fapply_mem_range _ _) rfl
        have := eq.mp ⟨a.pair b, hz, ?_⟩
        · obtain ⟨p, hp, p_def⟩ := this
          simp_rw [φ_ψ, pair_mem_fprod, pair_inj] at p_def
          obtain ⟨a', b', ha', hb', rfl, φa_φa', ψb_ψb'⟩ := p_def
          rw [←Subtype.ext_iff] at φa_φa' ψb_ψb'
          obtain ⟨⟩ := IsInjective.apply_inj hφ φ_bij.1 φa_φa'
          obtain ⟨⟩ := IsInjective.apply_inj hψ ψ_bij.1 ψb_ψb'
          exact hp
        · simp_rw [φ_ψ, pair_mem_fprod, pair_inj]
          simp only [exists_and_left, exists_and_right, existsAndEq, and_true, exists_eq_left']
          and_intros
          · use ha
          · use hb
      · obtain ⟨a, ha, b, hb, rfl⟩ := ‹y ⊆ A.prod B› hz |> mem_prod.mp
        letI φa : ZFSet := @ᶻφ ⟨a, by rwa [is_func_dom_eq hφ]⟩
        letI ψb : ZFSet := @ᶻψ ⟨b, by rwa [is_func_dom_eq hψ]⟩
        specialize eq (φa.pair ψb) φa (fapply_mem_range _ _) ψb (fapply_mem_range _ _) rfl
        have := eq.mpr ⟨a.pair b, hz, ?_⟩
        · obtain ⟨p, hp, p_def⟩ := this
          simp_rw [φ_ψ, pair_mem_fprod, pair_inj] at p_def
          obtain ⟨a', b', ha', hb', rfl, φa_φa', ψb_ψb'⟩ := p_def
          rw [←Subtype.ext_iff] at φa_φa' ψb_ψb'
          obtain ⟨⟩ := IsInjective.apply_inj hφ φ_bij.1 φa_φa'
          obtain ⟨⟩ := IsInjective.apply_inj hψ ψ_bij.1 ψb_ψb'
          exact hp
        · simp_rw [φ_ψ, pair_mem_fprod, pair_inj]
          simp only [exists_and_left, exists_and_right, existsAndEq, and_true, exists_eq_left']
          and_intros
          · use ha
          · use hb
    · intro Y hY
      rw [mem_powerset] at hY
      use φ_ψ⁻¹[Y]
      rw [mem_lambda]
      simp only [mem_powerset, pair_inj, existsAndEq, and_true, exists_eq_left', and_self_left]
      and_intros
      · intro z hz
        rw [mem_Image] at hz
        obtain ⟨hz, y, hy, yz⟩ := hz
        rw [mem_inv, pair_mem_fprod] at yz
        obtain ⟨a, b, ha, hb, rfl, rfl⟩ := yz
        exact hz
      · exact hY
      · rw [Image_of_composition_self_inv_of_bijective hφ_ψ hY]
  · apply lambda_isFunc
    intro S hS
    rw [mem_powerset] at hS ⊢
    intro z hz
    rw [mem_Image] at hz
    exact hz.1

end Auxiliary

end ZFSet
