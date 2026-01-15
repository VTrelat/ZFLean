import ZFLean.Functions

namespace ZFSet

section Isomorphisms

def isIso (A B : ZFSet) : Prop :=
  ∃ (bij : ZFSet) (is_func : A.IsFunc B bij), bij.IsBijective is_func
infix:40 " ≅ᶻ " => ZFSet.isIso

theorem isIso_refl : Reflexive ZFSet.isIso :=
  fun A ↦ ⟨A.Id, Id.IsFunc, Id.IsBijective⟩

instance : Trans ZFSet.isIso ZFSet.isIso ZFSet.isIso where
  trans := by
    intro x y z x_iso_y y_iso_z
    obtain ⟨bij, is_func, is_bij⟩ := x_iso_y
    obtain ⟨bij', is_func', is_bij'⟩ := y_iso_z
    set bij'' := ZFSet.composition bij' bij x y z
    exists bij'', ZFSet.IsFunc_of_composition_IsFunc is_func' is_func
    exact ZFSet.IsBijective.composition_of_bijective is_bij is_bij'

theorem isIso_symm : Symmetric ZFSet.isIso := by
  intro x y iso
  obtain ⟨bij, is_func, is_bij⟩ := iso
  have := is_func.1
  use bij⁻¹, ?_
  exact inv_bijective_of_bijective is_bij
instance : IsSymm ZFSet isIso where
  symm := isIso_symm

theorem isIso_trans : Transitive ZFSet.isIso := by
  intro x y z x_iso_y y_iso_z
  obtain ⟨bij, is_func, is_bij⟩ := x_iso_y
  obtain ⟨bij', is_func', is_bij'⟩ := y_iso_z
  set bij'' := ZFSet.composition bij' bij x y z
  exists bij'', ZFSet.IsFunc_of_composition_IsFunc is_func' is_func
  exact ZFSet.IsBijective.composition_of_bijective is_bij is_bij'
instance : IsTrans ZFSet isIso where
  trans := isIso_trans

theorem isIso_equiv : Equivalence ZFSet.isIso where
  refl := isIso_refl
  symm := @isIso_symm
  trans := @isIso_trans
instance : IsEquiv ZFSet isIso where
  refl := isIso_refl

section Lemmas

private def C (A B u : ZFSet) : ℕ → ZFSet
  | 0 => A \ B
  | n + 1 => B.sep fun y ↦ ∃ x ∈ C A B u n, x.pair y ∈ u

open Classical in
theorem bijective_of_injective_on_subset {A B : ZFSet}
  (B_sub : B ⊆ A) {u : ZFSet} {hu : A.IsFunc B u} (u_inj : IsInjective u) :
    ∃ (v : ZFSet) (hv : A.IsFunc B v), IsBijective v := by
  let C₀ := A \ B

  have C_sub {n} : C A B u n ⊆ A := by
    induction n with
    | zero =>
      intro x x_mem_C
      rw [C, mem_diff] at x_mem_C
      exact x_mem_C.1
    | succ n ih =>
      intro x x_mem_C
      rw [C, mem_sep] at x_mem_C
      exact B_sub x_mem_C.1

  let v := λᶻ : A → B
              | x ↦ if mem_Cn : ∃ n, x ∈ C A B u n then @ᶻu ⟨x, by
                      rw [is_func_dom_eq hu]
                      obtain ⟨_, x_mem_Cn⟩ := mem_Cn
                      apply C_sub x_mem_Cn⟩
                    else x

  have hv : A.IsFunc B v := by
    apply lambda_isFunc
    intro x xA
    split_ifs with mem_Cn
    · apply fapply_mem_range
    · push_neg at mem_Cn
      specialize mem_Cn 0
      rw [C, mem_diff, not_and, not_not] at mem_Cn
      exact mem_Cn xA
  have v_inj : IsInjective v := by
    intro x y z hx hy hz eq₁ eq₂
    rw [lambda_spec] at eq₁ eq₂
    split_ifs at eq₁ eq₂ with mem_x mem_y mem_y <;> (
      obtain ⟨-, -, rfl⟩ := eq₁
      obtain ⟨-, -, eq⟩ := eq₂)
    · generalize_proofs u_pfun x_dom y_dom at eq
      rw [SetLike.coe_eq_coe] at eq
      obtain ⟨⟩ := IsInjective.apply_inj hu u_inj eq
      rfl
    · generalize_proofs u_pfun u_rel x_dom at eq
      subst y
      obtain ⟨n, mem_x⟩ := mem_x
      push_neg at mem_y
      specialize mem_y (n+1)
      rw [C, mem_sep, not_and] at mem_y
      specialize mem_y hz
      push_neg at mem_y
      specialize mem_y x mem_x
      nomatch mem_y <| fapply.def u_pfun x_dom
    · generalize_proofs u_pfun u_rel y_dom at eq
      subst z
      obtain ⟨n, mem_y⟩ := mem_y
      push_neg at mem_x
      specialize mem_x (n+1)
      rw [C, mem_sep, not_and] at mem_x
      specialize mem_x hz
      push_neg at mem_x
      specialize mem_x y mem_y
      nomatch mem_x <| fapply.def u_pfun y_dom
    · exact eq

  have v_surj : IsSurjective v := by classical
    intro y yB
    by_cases y_mem_C : ∃ n, y ∈ C A B u n
    · obtain ⟨n, y_mem_Cn⟩ := y_mem_C
      have : n ≠ 0 := by
        rintro rfl
        rw [C, mem_diff] at y_mem_Cn
        nomatch y_mem_Cn.2 yB
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [C, mem_sep] at y_mem_Cn
      obtain ⟨-, x, x_mem_Cn, x_y_u⟩ := y_mem_Cn
      use x, C_sub x_mem_Cn
      rw [lambda_spec]
      and_intros
      · exact C_sub x_mem_Cn
      · exact yB
      · rw [dite_cond_eq_true <| eq_true ⟨n, x_mem_Cn⟩,
          fapply.of_pair (is_func_is_pfunc hu) x_y_u]
    · use y, B_sub yB
      rw [lambda_spec]
      and_intros
      · exact B_sub yB
      · exact yB
      · rw [dite_cond_eq_false <| eq_false y_mem_C]
  use v, hv, v_inj, v_surj

set_option pp.proofs true in
/--
Cantor–Bernstein theorem: if there are injective functions
`f : A → B` and `g : B → A`, then `A` and `B` are isomorphic.
-/
theorem isIso_of_biembedding {E F f g : ZFSet} {hf : E.IsFunc F f}
  (f_inj : IsInjective f) {hg : F.IsFunc E g} (g_inj : IsInjective g hg) : E ≅ᶻ F := by
  let B := g.Range
  have B_sub : B ⊆ E := sep_subset_self
  let u := composition g f E F B
  have hu : E.IsFunc B u := ZFSet.IsFunc_of_composition_IsFunc (IsFunc.is_func_on_range hg) hf
  have u_inj : IsInjective u := by
    intro x y z hx hy hz eq₁ eq₂
    unfold u at eq₁ eq₂
    simp only [composition, mem_sep, mem_prod, pair_inj, exists_eq_right_right', existsAndEq,
      and_true, exists_eq_left'] at eq₁ eq₂
    obtain ⟨-, x', hx', x_x'_f, x'_z_g⟩ := eq₁
    obtain ⟨-, y', hy', y_y'_f, y'_z_g⟩ := eq₂
    obtain rfl := g_inj x' y' z hx' hy' (B_sub hz) x'_z_g y'_z_g
    exact f_inj x y x' hx hy hx' x_x'_f y_y'_f
  obtain ⟨v, hv, bij⟩ := bijective_of_injective_on_subset B_sub u_inj

  have hg' : F.IsFunc B g := IsFunc.is_func_on_range hg
  have g_bij : IsBijective g hg' := bijective_of_injective hg g_inj
  have h_v_hinv : E.IsFunc F (composition (inv g hg'.1) v E B F) :=
    IsFunc_of_composition_IsFunc (inv_is_func_of_bijective g_bij) hv

  use composition (inv g hg'.1) v E B F, h_v_hinv

  exact IsBijective.composition_of_bijective bij (inv_bijective_of_bijective g_bij)

alias schroeder_bernstein := isIso_of_biembedding

theorem isIso_of_prod {A B C D : ZFSet} (h : A ≅ᶻ C) (h' : B ≅ᶻ D) : A.prod B ≅ᶻ C.prod D := by
  obtain ⟨f₁, hf₁, bij₁⟩ := h
  obtain ⟨f₂, hf₂, bij₂⟩ := h'
  let F := (A.prod B).prod (C.prod D) |>.sep fun z ↦
    ∃ (a b c d : ZFSet), z = (a.pair b).pair (c.pair d) ∧ (a.pair c ∈ f₁) ∧ (b.pair d ∈ f₂)
  use F, ?_
  · and_intros
    · intro ab a'b' cd hab ha'b' hcd habcd ha'b'cd
      simp only [mem_sep, mem_prod, pair_inj, exists_eq_right_right', F] at habcd ha'b'cd
      obtain ⟨⟨⟨a, ha, b, hb, rfl⟩, c, hc, d, hd, rfl⟩, _, _, _, _, ⟨ab_eq, cd_eq⟩, ac_f₁, bd_f₂⟩ :=
        habcd
      rw [pair_inj] at ab_eq cd_eq
      rcases ab_eq with ⟨rfl, rfl⟩
      rcases cd_eq with ⟨rfl, rfl⟩

      obtain ⟨⟨⟨a', ha', b', hb', rfl⟩, -⟩, _, _, _, _, ⟨a'b'_eq, cd_eq⟩, a'c_f₁, b'd_f₂⟩ := ha'b'cd
      rw [pair_inj] at a'b'_eq cd_eq
      rcases a'b'_eq with ⟨rfl, rfl⟩
      rcases cd_eq with ⟨rfl, rfl⟩
      congr
      · exact bij₁.1 _ _ _ ha ha' hc ac_f₁ a'c_f₁
      · exact bij₂.1 _ _ _ hb hb' hd bd_f₂ b'd_f₂
    · intro cd hcd
      rw [mem_prod] at hcd
      obtain ⟨c, hc, d, hd, rfl⟩ := hcd
      obtain ⟨a, ha, ac_f₁⟩ := bij₁.2 c hc
      obtain ⟨b, hb, bd_f₂⟩ := bij₂.2 d hd
      use a.pair b
      and_intros
      · rw [pair_mem_prod]
        exact ⟨ha, hb⟩
      · simp only [mem_sep, mem_prod, pair_inj, exists_eq_right_right', existsAndEq, and_true,
        exists_eq_left', F]
        and_intros
        · exact ha
        · exact hb
        · exact hc
        · exact hd
        · exact ac_f₁
        · exact bd_f₂
  · and_intros
    · intro z hz
      rw [mem_sep] at hz
      exact hz.1
    · intro z hz
      rw [mem_prod] at hz
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      obtain ⟨c, hc, c_unq⟩ := hf₁.2 a ha
      obtain ⟨d, hd, d_unq⟩ := hf₂.2 b hb
      use c.pair d
      and_intros <;> beta_reduce
      · rw [mem_sep, pair_mem_prod, pair_mem_prod, pair_mem_prod]
        and_intros
        · exact ha
        · exact hb
        · exact hf₁.1 hc |> pair_mem_prod.mp |>.2
        · exact hf₂.1 hd |> pair_mem_prod.mp |>.2
        · use a, b, c, d
      · intro y hy
        rw [mem_sep, pair_mem_prod] at hy
        obtain ⟨c', hc', d', hd', rfl⟩ := hy.1.2 |> mem_prod.mp
        simp only [mem_prod, pair_inj, exists_eq_right_right', existsAndEq, and_true,
          exists_eq_left'] at hy
        congr
        · apply c_unq
          exact hy.2.1
        · apply d_unq
          exact hy.2.2

theorem inv_Image_of_bijective {f A B : ZFSet} {hf : A.IsFunc B f}
  (bij : f.IsBijective) {X : ZFSet} (hX : X ⊆ A) :
    f⁻¹[(f[X])] = X := by
  ext1 x
  constructor <;> intro hx
  · simp [mem_Image, mem_inv] at hx
    obtain ⟨xA, y, ⟨yB, u, uX, fuy⟩, fxy⟩ := hx
    obtain rfl := bij.1 u x y (hf.1 fuy |> pair_mem_prod.mp |>.1) xA yB fuy fxy
    exact uX
  · simp [mem_Image, mem_inv]
    and_intros
    · exact hX hx
    · obtain ⟨y, yB, -⟩ := hf.2 x (hX hx)
      use y
      and_intros
      · exact hf.1 yB |> pair_mem_prod.mp |>.2
      · use x
      · exact yB

theorem Image_inv_of_bijective {f A B : ZFSet} {hf : A.IsFunc B f}
  (bij : f.IsBijective hf) {X : ZFSet} (hX : X ⊆ B) :
    f[(f⁻¹[X])] = X := by
  let g := f⁻¹
  have hg : B.IsFunc A g := inv_is_func_of_bijective bij
  have gbij : g.IsBijective hg := inv_bijective_of_bijective bij
  have ginv_eq : g⁻¹ = f := by rw [inv_involutive]
  have := inv_Image_of_bijective gbij hX
  dsimp [g] at this
  conv at this =>
    enter [1,1]
    rw [inv_involutive]
  exact this

theorem IsInjective_of_left_inverse {A B : ZFSet} {f : ZFSet}
  (hf : A.IsFunc B f) {g : ZFSet} (hg : B.IsFunc A g) (left_inv : g ∘ᶻ f = 𝟙A) :
    IsInjective f := by
  intro x y z hx hy hz fxy fxz
  have x_x : x.pair x ∈ g ∘ᶻ f := by
    rw [left_inv]
    exact pair_self_mem_Id hx
  have y_y : y.pair y ∈ g ∘ᶻ f := by
    rw [left_inv]
    exact pair_self_mem_Id hy

  simp only [composition, mem_sep, mem_prod, pair_inj, exists_eq_right_right', and_self,
    existsAndEq, and_true, exists_eq_left'] at x_x y_y
  obtain ⟨-, x', hx', x_x'_f, x'_x_g⟩ := x_x
  obtain ⟨-, y', hy', y_y'_f, y'_y_g⟩ := y_y

  obtain rfl : x' = y' := by
    trans z
    · apply hf.2 x hx |>.unique
      · exact x_x'_f
      · exact fxy
    · apply hf.2 y hy |>.unique
      · exact fxz
      · exact y_y'_f
  apply hg.2 x' hx' |>.unique
  · exact x'_x_g
  · exact y'_y_g

theorem IsSurjective_of_right_inverse {A B : ZFSet} {f : ZFSet}
  (hf : A.IsFunc B f) {g : ZFSet} (hg : B.IsFunc A g) (right_inv : f ∘ᶻ g = 𝟙B) :
    IsSurjective f := by
  intro y yB
  have y_y : y.pair y ∈ f ∘ᶻ g := by
    rw [right_inv]
    exact pair_self_mem_Id yB
  simp only [composition, mem_sep, mem_prod, pair_inj, exists_eq_right_right', and_self,
    existsAndEq, and_true, exists_eq_left'] at y_y
  obtain ⟨yB, x, xA, gyx, fxy⟩ := y_y
  use x, xA

theorem isIso_of_two_sided_inverse {A B : ZFSet} {f : ZFSet}
  {hf : A.IsFunc B f} {g : ZFSet} {hg : B.IsFunc A g}
  (left_inv : g ∘ᶻ f = 𝟙A) (right_inv : f ∘ᶻ g = 𝟙B) :
    A ≅ᶻ B := by
  use f, hf
  and_intros
  · exact IsInjective_of_left_inverse _ _ left_inv
  · exact IsSurjective_of_right_inverse _ _ right_inv

theorem isIso_powerset {A B : ZFSet} (h : A ≅ᶻ B) : A.powerset ≅ᶻ B.powerset := by
  obtain ⟨f, hf, bij⟩ := h
  let F := λᶻ : A.powerset → B.powerset | x ↦ f[x]
  have hF : A.powerset.IsFunc B.powerset F := by
    apply lambda_isFunc
    intros
    rw [mem_powerset]
    intro y yIm
    rw [mem_Image] at yIm
    exact yIm.1
  let F' := λᶻ : B.powerset → A.powerset | z ↦ f⁻¹[z]
  have hF' : B.powerset.IsFunc A.powerset F' := by
    apply lambda_isFunc
    intros
    rw [mem_powerset]
    intro y yIm
    rw [mem_Image] at yIm
    exact yIm.1
  have left_inv : F' ∘ᶻ F = 𝟙A.powerset := by
    ext1 X
    rw [fcomp, composition, mem_sep, mem_prod]
    constructor
    · rintro ⟨⟨X, hX, Y, hY, rfl⟩, ⟨_, _, eq, Z, hZ, FXZ, F'ZY⟩⟩
      rw [pair_inj] at eq
      obtain ⟨rfl, rfl⟩ := eq
      rw [mem_lambda] at FXZ F'ZY
      simp only [pair_inj, mem_powerset, existsAndEq, and_true, exists_eq_left'] at FXZ F'ZY
      obtain ⟨-, -, rfl⟩ := FXZ
      obtain ⟨-, -, rfl⟩ := F'ZY
      rw [inv_Image_of_bijective bij (mem_powerset.mp hX), pair_mem_Id_iff hX]
    · intro hX
      rw [mem_Id_iff] at hX
      obtain ⟨X, hX, rfl⟩ := hX
      simp only [mem_powerset, pair_inj, exists_eq_right_right', and_self, existsAndEq,
        and_true, exists_eq_left']
      apply And.intro <| mem_powerset.mp hX
      use f[X]
      and_intros
      · intro z hz
        rw [mem_Image] at hz
        exact hz.1
      · rw [lambda_spec]
        and_intros
        · exact hX
        · rw [mem_powerset]
          intro y hy
          rw [mem_Image] at hy
          exact hy.1
        · rfl
      · rw [lambda_spec]
        and_intros
        · rw [mem_powerset]
          intro y hy
          rw [mem_Image] at hy
          exact hy.1
        · exact hX
        · rw [inv_Image_of_bijective bij (mem_powerset.mp hX)]

  have right_inv : F ∘ᶻ F' = 𝟙B.powerset := by
    ext1 X
    rw [fcomp, composition, mem_sep, mem_prod]
    constructor
    · rintro ⟨⟨X, hX, Y, hY, rfl⟩, ⟨_, _, eq, Z, hZ, FXZ, F'ZY⟩⟩
      rw [pair_inj] at eq
      obtain ⟨rfl, rfl⟩ := eq
      rw [mem_lambda] at FXZ F'ZY
      simp only [pair_inj, mem_powerset, existsAndEq, and_true, exists_eq_left'] at FXZ F'ZY
      obtain ⟨-, -, rfl⟩ := FXZ
      obtain ⟨-, -, rfl⟩ := F'ZY
      rw [Image_inv_of_bijective bij (mem_powerset.mp hX), pair_mem_Id_iff hX]
    · intro hX
      rw [mem_Id_iff] at hX
      obtain ⟨X, hX, rfl⟩ := hX
      simp only [mem_powerset, pair_inj, exists_eq_right_right', and_self, existsAndEq,
        and_true, exists_eq_left']
      apply And.intro <| mem_powerset.mp hX
      have := subset_prod_inv hf.1
      use f⁻¹[X]
      and_intros
      · intro z hz
        rw [mem_Image] at hz
        exact hz.1
      · rw [lambda_spec]
        and_intros
        · exact hX
        · rw [mem_powerset]
          intro y hy
          rw [mem_Image] at hy
          exact hy.1
        · rfl
      · rw [lambda_spec]
        and_intros
        · rw [mem_powerset]
          intro y hy
          rw [mem_Image] at hy
          exact hy.1
        · exact hX
        · rw [Image_inv_of_bijective bij (mem_powerset.mp hX)]
  apply isIso_of_two_sided_inverse left_inv right_inv

open Classical in
theorem isIso_funs_to_pow_rel {A B : ZFSet} : A.funs B.powerset ≅ᶻ (A.prod B).powerset := by
  let F := λᶻ : (A.funs B.powerset) → (A.prod B).powerset
              |         f           ↦ if hf : A.IsFunc B.powerset f then
                                        A.prod B |>.sep fun z ↦
                                          if hz : z ∈ A.prod B then
                                            have : z.π₁ ∈ A := by
                                              rw [mem_prod] at hz
                                              obtain ⟨_, _, _, _, rfl⟩ := hz
                                              rwa [π₁_pair]
                                            z.π₂ ∈ (@ᶻf ⟨z.π₁, by rwa [is_func_dom_eq hf]⟩).val
                                          else False
                                      else ∅
  let G := λᶻ : (A.prod B).powerset → (A.funs B.powerset)
              |         R           ↦ λᶻ: A → B.powerset
                                        | a ↦ if ha : a ∈ A then
                                                B.sep fun b ↦ (a.pair b ∈ R) -- {b ∈ B | (a, b) ∈ R}
                                              else ∅

  have hF : (A.funs B.powerset).IsFunc (A.prod B).powerset F := by
    apply lambda_isFunc
    intro f hf
    rw [mem_funs] at hf
    rw [dite_cond_eq_true (eq_true hf)]
    apply sep_mem_powerset
    rw [mem_powerset]
  have hG : (A.prod B).powerset.IsFunc (A.funs B.powerset) G := by
    apply lambda_isFunc
    intro R hR
    rw [mem_powerset] at hR
    apply mem_funs_of_lambda
    intro a ha
    rw [dite_cond_eq_true (eq_true ha)]
    apply sep_mem_powerset
    rw [mem_powerset]

  apply isIso_of_two_sided_inverse (f := F) (g := G)
  · ext1 f
    simp only [mem_composition, mem_funs, mem_powerset, mem_Id_iff]
    constructor
    · rintro ⟨f, R, g, rfl, hf, hg, hR, fR_F, Rg_G⟩
      use f, hf
      rw [pair_inj, eq_self, true_and]
      rw [lambda_spec] at fR_F Rg_G
      obtain ⟨_, _, rfl⟩ := fR_F
      obtain ⟨_, _, rfl⟩ := Rg_G
      rw [dite_cond_eq_true (eq_true hf)]
      conv_rhs => rw [lambda_eta hf]
      rw [lambda_ext_iff ?_]
      · intro a ha
        rw [dite_cond_eq_true (eq_true ha), dite_cond_eq_true (eq_true ha)]
        ext1 X
        simp only [mem_prod, dite_else_false, mem_sep, pair_inj, exists_eq_right_right', π₁_pair,
          π₂_pair, and_exists_self]
        constructor
        · rintro ⟨_, _, hX⟩
          exact hX
        · intro hX
          obtain ⟨Y, Y_def, X_unq⟩ := hf.2 a ha
          have YB := hf.1 Y_def |> pair_mem_prod.mp |>.2
          rw [Image_of_singleton_pair_mem_iff hf] at Y_def
          simp_rw [fapply_eq_Image_singleton hf ha, Y_def, sInter_singleton] at hX ⊢
          rw [mem_powerset] at YB
          and_intros
          · exact YB hX
          · exact ⟨⟨ha, YB hX⟩, hX⟩
      · intro a ha
        rw [dite_cond_eq_true (eq_true ha)]
        apply sep_mem_powerset
        rw [mem_powerset]
    · rintro ⟨f, hf, rfl⟩
      use f, @ᶻF ⟨f, by rwa [is_func_dom_eq hF, mem_funs]⟩, f
      · rw [eq_self, true_and, ←and_assoc, and_self]
        and_intros
        · exact hf.1
        · exact hf.2
        · rw [←mem_powerset]
          apply fapply_mem_range
        · apply fapply.def
        · rw [lambda_spec]
          and_intros
          · apply fapply_mem_range
          · rw [mem_funs]
            exact hf
          · conv_lhs => rw [lambda_eta hf]
            rw [lambda_ext_iff ?_]
            · intro a ha
              generalize_proofs _ _ ha_f_dom Fpfunc f_Fdom
              rw [fapply_lambda (ha := by rwa [mem_funs]), dite_cond_eq_true (eq_true ha),
                dite_cond_eq_true (eq_true ha),
                dite_cond_eq_true (eq_true hf)]
              · ext1 z
                constructor
                · intro hz
                  simp only [mem_prod, dite_else_false, mem_sep, pair_inj, exists_eq_right_right',
                    π₁_pair, π₂_pair, and_exists_self]
                  have zB : z ∈ B := mem_powerset.mp (fapply_mem_range _ (ha_f_dom ha)) hz
                  exact ⟨zB, ⟨ha, zB⟩, hz⟩
                · intro hz
                  simp only [mem_prod, dite_else_false, mem_sep, pair_inj, exists_eq_right_right',
                    π₁_pair, π₂_pair, and_exists_self] at hz
                  obtain ⟨-, _, z_mem⟩ := hz
                  exact z_mem
              · intro X hX
                rw [dite_cond_eq_true (eq_true <| mem_funs.mp hX)]
                apply sep_mem_powerset
                rw [mem_powerset]
            · intro a ha
              rw [dite_cond_eq_true (eq_true ha)]
              apply fapply_mem_range
  · ext1 R
    simp only [mem_composition, mem_powerset, mem_funs, mem_Id_iff]
    constructor
    · rintro ⟨R, f, S, rfl, hR, hf, hS, Rf_G, fS_F⟩
      use R, hR
      rw [pair_inj, eq_self, true_and]
      rw [lambda_spec] at Rf_G fS_F
      obtain ⟨_, _, rfl⟩ := Rf_G
      obtain ⟨_, _, rfl⟩ := fS_F
      rw [dite_cond_eq_true (eq_true hS)]
      ext1 ab
      simp only [mem_prod, dite_eq_ite, dite_else_false, mem_sep, and_exists_self]
      constructor
      · rintro ⟨⟨a, ha, b, hb, rfl⟩, b_mem⟩
        simp only [π₁_pair, π₂_pair] at b_mem
        rw [fapply_lambda] at b_mem
        · rw [ite_cond_eq_true (h := eq_true ha), mem_sep] at b_mem
          exact b_mem.2
        · intro x hx
          rw [ite_cond_eq_true (h := eq_true hx)]
          apply sep_mem_powerset
          rw [mem_powerset]
        · exact ha
      · intro hab
        obtain ⟨a, ha, b, hb, rfl⟩ := hR hab |> mem_prod.mp
        simp only [π₁_pair, π₂_pair, pair_inj, exists_eq_right_right']
        use ⟨ha, hb⟩
        rw [fapply_lambda]
        · rw [ite_cond_eq_true (h := eq_true ha), mem_sep]
          exact ⟨hb, hab⟩
        · intro x hx
          rw [ite_cond_eq_true (h := eq_true hx)]
          apply sep_mem_powerset
          rw [mem_powerset]
        · exact ha
    · rintro ⟨S, hS, rfl⟩
      simp only [pair_inj, existsAndEq, and_true, exists_and_left, exists_eq_left', and_self_left]
      and_intros
      · exact hS
      · use @ᶻG ⟨S, by rwa [is_func_dom_eq hG, mem_powerset]⟩
        and_intros
        · exact fapply_mem_range _ _ |> mem_funs.mp |>.1
        · intro a ha
          rw [fapply_lambda]
          · simp only [ha, true_and, dite_true, lambda_spec, mem_powerset]
            use B.sep fun b ↦ (a.pair b ∈ S)
            and_intros
            · exact sep_subset_self
            · rfl
            · rintro _ ⟨_, rfl⟩
              rfl
          · intros
            apply mem_funs_of_lambda
            intro _ ha
            rw [dite_cond_eq_true (eq_true ha)]
            apply sep_mem_powerset
            rw [mem_powerset]
          · rwa [mem_powerset]
        · apply fapply.def
        · rw [lambda_spec]
          and_intros
          · apply fapply_mem_range
          · rwa [mem_powerset]
          · rw [dite_cond_eq_true (eq_true ?_)]
            · ext1 ab
              simp only [mem_prod, dite_else_false, mem_sep, and_exists_self]
              generalize_proofs G_pfunc _ S_Gdom fapply_pfunc a_dom
              have fapp_eq :
                ↑(@ᶻG ⟨S, S_Gdom⟩) =
                (λᶻ : A → B.powerset
                    | a ↦ if ha : a ∈ A then B.sep (fun b => a.pair b ∈ S) else ∅)
                  := by
                rw [fapply_lambda]
                · intros
                  apply mem_funs_of_lambda
                  intro _ ha
                  rw [dite_cond_eq_true (eq_true ha)]
                  apply sep_mem_powerset
                  rw [mem_powerset]
                · rwa [mem_powerset]
              constructor
              · intro hab
                obtain ⟨a, ha, b, hb, rfl⟩ := hS hab |> mem_prod.mp
                simp only [π₁_pair, π₂_pair, pair_inj, exists_eq_right_right']
                use ⟨ha, hb⟩
                rw [fapply]
                generalize_proofs choose₁ choose₂
                simp [fapp_eq] at *
                clear fapp_eq
                generalize_proofs choose₃
                have choose₃_spec := choose_spec choose₃
                rw [lambda_spec, ite_cond_eq_true _ _ (eq_true ha)] at choose₃_spec
                rw [choose₃_spec.2.2.2, mem_sep]
                exact ⟨hb, hab⟩
              · rintro ⟨⟨a, ha, b, hb, rfl⟩, h⟩
                simp only [π₁_pair, π₂_pair] at h
                simp only [fapply, mem_powerset, mem_funs] at h
                generalize_proofs choose₁ choose₂ at h
                have choose₁_spec := choose_spec choose₁
                have choose₂_spec := choose_spec choose₂
                have choose₁_eq := choose₁_spec.2 |> lambda_spec.mp |>.2.2

                conv at choose₂_spec =>
                  enter [2,1]
                  rw [choose₁_eq]
                rw [lambda_spec, dite_cond_eq_true (eq_true ha)] at choose₂_spec
                rw [choose₂_spec.2.2.2, mem_sep] at h
                exact h.2
            · rw [fapply_lambda]
              · apply lambda_isFunc
                intro a ha
                rw [dite_cond_eq_true (eq_true ha)]
                apply sep_mem_powerset
                rw [mem_powerset]
              · intros
                apply mem_funs_of_lambda
                intro a ha
                rw [dite_cond_eq_true (eq_true ha)]
                apply sep_mem_powerset
                rw [mem_powerset]
              · rwa [mem_powerset]

  · exact hF
  · exact hG

theorem isIso_of_funs {A B C D : ZFSet} (h : A ≅ᶻ C) (h' : B ≅ᶻ D) : A.funs B ≅ᶻ C.funs D := by
  classical
  obtain ⟨F, hF, Fbij⟩ := h
  have : F⁻¹ ⊆ C.prod A := by apply subset_prod_inv
  obtain ⟨G, hG, Gbij⟩ := h'

  let ξ := λᶻ : (A.funs B) → (C.funs D)
              |     f      ↦ if hf : f ⊆ A.prod B then
                              λᶻ: C → D
                                | c ↦ ⋂₀ (G[f[F⁻¹[{c}]]])
                            else ∅
  use ξ, ?_
  · rw [bijective_exists1_iff]
    intro f hf
    rw [mem_funs] at hf
    have Ginv_isfunc := inv_is_func_of_bijective Gbij
    let g := λᶻ : A → B
                | a ↦ if ha : a ∈ A then ⋂₀ (G⁻¹[f[F[{a}]]]) else ∅
    have hg : A.IsFunc B g := by
      apply lambda_isFunc
      intro a ha
      rw [dite_cond_eq_true (eq_true ha),
        Image_singleton_eq_fapply hF ha,
        Image_singleton_eq_fapply hf (by apply fapply_mem_range),
        Image_singleton_eq_fapply Ginv_isfunc (by apply fapply_mem_range),
        sInter_singleton]
      apply fapply_mem_range
    use g
    and_intros
    · apply mem_funs_of_lambda
      intro a ha
      rw [dite_cond_eq_true (eq_true ha),
        Image_singleton_eq_fapply hF ha,
        Image_singleton_eq_fapply hf (by apply fapply_mem_range),
        Image_singleton_eq_fapply Ginv_isfunc (by apply fapply_mem_range),
        sInter_singleton]
      apply fapply_mem_range
    · rw [lambda_spec]
      and_intros
      · rw [mem_funs]
        exact hg
      · rw [mem_funs]
        exact hf
      · rw [dite_cond_eq_true (eq_true hg.1), lambda_eta hf, lambda_ext_iff]
        · intro c hc
          rw [dite_cond_eq_true (eq_true hc)]
          rw [Image_singleton_eq_fapply (inv_is_func_of_bijective Fbij) hc,
            Image_singleton_eq_fapply hg (by apply fapply_mem_range),
            Image_singleton_eq_fapply hG (by apply fapply_mem_range),
            sInter_singleton]
          conv =>
            unfold fapply
            dsimp
            rfl
          congr
          funext d
          ext
          constructor <;> (rintro ⟨xD, h⟩; refine ⟨xD, ?_⟩)
          · generalize_proofs Frel c_Finv c_Finv_g
            have ⟨bB, ab_g⟩ := Classical.choose_spec c_Finv_g
            have ⟨aA, ac_F⟩ := Classical.choose_spec c_Finv
            set b := Classical.choose c_Finv_g
            set a := Classical.choose c_Finv
            rw [mem_inv] at ac_F
            rw [lambda_spec] at ab_g
            obtain ⟨-, -, b_eq⟩ := ab_g
            rw [dite_cond_eq_true (eq_true aA)] at b_eq
            have Fa := fapply.of_pair (is_func_is_pfunc hF) ac_F
            have Fc := fapply.of_pair (is_func_is_pfunc hf) h
            conv at b_eq =>
              enter [2]
              rw [Image_singleton_eq_fapply hF aA, Fa, Image_singleton_eq_fapply hf hc, Fc,
                ←fapply_eq_Image_singleton Ginv_isfunc xD]
            rw [b_eq, ←mem_inv (is_rel_of_is_func hG)]
            apply fapply.def
          · generalize_proofs Frel ac_Finv ab_g_spec at h
            have ⟨aA, ac_F⟩ := Classical.choose_spec ac_Finv
            have ⟨bB, ab_g⟩ := Classical.choose_spec ab_g_spec
            set b := Classical.choose ab_g_spec
            set a := Classical.choose ac_Finv
            rw [lambda_spec] at ab_g
            obtain ⟨-, -, b_eq⟩ := ab_g
            rw [dite_cond_eq_true (eq_true aA)] at b_eq
            rw [mem_inv] at ac_F
            have Fa := fapply.of_pair (is_func_is_pfunc hF) ac_F
            have Gb := fapply.of_pair (is_func_is_pfunc hG) h
            conv at b_eq =>
              enter [2]
              rw [Image_singleton_eq_fapply hF aA, Fa, Image_singleton_eq_fapply hf hc,
                Image_singleton_eq_fapply Ginv_isfunc (fapply_mem_range _ _), sInter_singleton]
            simp only [b_eq, Subtype.ext_iff] at Gb
            conv at Gb =>
              enter [1,1]
              rw [←fapply_composition hG Ginv_isfunc (fapply_mem_range _ _)]
              unfold fapply
            dsimp at Gb
            generalize_proofs Grel cdf cd_GGinv at Gb
            subst d
            have ⟨dD, cd_G⟩ := Classical.choose_spec cd_GGinv
            have ⟨d'D, cd_f⟩ := Classical.choose_spec cdf
            set d := Classical.choose cd_GGinv
            set d' := Classical.choose cdf
            rw [composition_inv_self_of_bijective Gbij, pair_mem_Id_iff d'D] at cd_G
            rwa [←cd_G]
        · intro c hc
          rw [dite_cond_eq_true (eq_true hc)]
          apply fapply_mem_range
    · rintro g' ⟨hg', g'f_ξ⟩
      rw [lambda_spec] at g'f_ξ
      obtain ⟨-,-,f_eq⟩ := g'f_ξ
      rw [dite_cond_eq_true (eq_true (by rw [mem_funs] at hg'; exact hg'.1))] at f_eq
      subst f_eq
      rw [lambda_eta (mem_funs.mp hg'), lambda_ext_iff]
      · intro a ha
        simp only [dite_cond_eq_true (eq_true ha)]
        rw [Image_singleton_eq_fapply hF ha,
          Image_singleton_eq_fapply hf (by apply fapply_mem_range),
          Image_singleton_eq_fapply Ginv_isfunc (by apply fapply_mem_range),
          sInter_singleton]
        conv_rhs =>
          unfold fapply
        dsimp
        generalize_proofs g'pfunc g'rel a_g'dom Grel Frel acF dclambda bdGinv
        have ⟨cC, ac_F⟩ := Classical.choose_spec acF
        have ⟨bB, db_G⟩ := Classical.choose_spec bdGinv
        have ⟨dD, dc_eq⟩:= Classical.choose_spec dclambda
        set! d := Classical.choose dclambda with d_def
        set! b := Classical.choose bdGinv with b_def
        set! c := Classical.choose acF with c_def
        rw [lambda_spec] at dc_eq
        obtain ⟨-, -, d_eq⟩ := dc_eq
        conv_lhs at d_eq => rw [←d_def]
        rw [←mem_inv] at ac_F
        conv at ac_F =>
          conv =>
            lhs
            change inv F
          rw [←c_def]
        conv at d_eq =>
          conv =>
            enter [2,1,2]
            conv =>
              enter [2]
              rw [←c_def, Image_singleton_eq_fapply (inv_is_func_of_bijective Fbij) cC]
              simp only [←c_def, fapply.of_pair _ ac_F]
          conv =>
            enter [2]
            conv =>
              enter [1,2]
              rw [Image_singleton_eq_fapply (mem_funs.mp hg') ha]
            rw [←fapply_eq_Image_singleton hG (fapply_mem_range g'pfunc a_g'dom)]
        rw [←b_def, ←d_def] at db_G
        have b_eq := fapply.of_pair (is_func_is_pfunc Ginv_isfunc) db_G
        rw [Subtype.ext_iff] at b_eq
        simp [d_eq] at b_eq
        rw [←fapply_composition Ginv_isfunc hG (fapply_mem_range g'pfunc a_g'dom)] at b_eq
        conv at b_eq =>
          unfold fapply
          dsimp
        generalize_proofs abg' bb'GGinv at b_eq
        have ⟨bB', bb'⟩ := Classical.choose_spec bb'GGinv
        have ⟨g'B, ab_g'⟩ := Classical.choose_spec abg'
        set b := Classical.choose bb'GGinv
        set b' := Classical.choose abg'
        rw [composition_self_inv_of_bijective Gbij, pair_mem_Id_iff g'B] at bb'
        rw [←b_def, ←b_eq, ←bb']
        rfl
      · intro _ h
        rw [dite_cond_eq_true (eq_true h)]
        apply fapply_mem_range
  · and_intros
    · exact lambda_subset
    · intro f hf
      rw [mem_funs] at hf
      use λᶻ : C → D
             | c ↦ ⋂₀ (G[f[F⁻¹[{c}]]])
      and_intros <;> beta_reduce
      · rw [lambda_spec]
        and_intros
        · rwa [mem_funs]
        · apply mem_funs_of_lambda
          intro c hc
          obtain ⟨a, ha, a_def⟩ := eq_singleton_of_bijective_inv_Image_of_singleton Fbij hc
          obtain ⟨b, hb, b_def⟩ : ∃ b ∈ B, f[{a}] = {b} := by
            obtain ⟨b, hb, b_unq⟩ := hf.2 a ha
            use b
            and_intros
            · exact hf.1 hb |> pair_mem_prod.mp |>.2
            · rwa [←Image_of_singleton_pair_mem_iff hf]
          obtain ⟨d, hd, d_def⟩ : ∃ d ∈ D, G[{b}] = {d} := by
            obtain ⟨d, hd, d_unq⟩ := hG.2 b hb
            use d
            and_intros
            · exact hG.1 hd |> pair_mem_prod.mp |>.2
            · rwa [←Image_of_singleton_pair_mem_iff hG]
          rwa [a_def, b_def, d_def, sInter_singleton]
        · rw [dite_cond_eq_true (eq_true hf.1)]
      · intro g hg
        rw [lambda_spec, dite_cond_eq_true (eq_true hf.1)] at hg
        exact hg.2.2

theorem isIso_powerset_char_pred {A : ZFSet} : A.powerset ≅ᶻ A.funs 𝔹 := by
  apply isIso_symm
  let f := λᶻ : (A.funs 𝔹) → (A.powerset)
              |         fX ↦ A.sep fun z ↦ z.pair zftrue ∈ fX
  use f, ?_
  · and_intros
    · intro fX fY Z hfX hfY hZ fX_Z fY_Z
      rw [mem_lambda] at fX_Z fY_Z
      obtain ⟨_, X, eq, -, _, rfl⟩ := fX_Z
      rw [pair_inj] at eq
      obtain ⟨rfl, rfl⟩ := eq
      obtain ⟨_, Y, eq, -, _, rfl⟩ := fY_Z
      rw [pair_inj] at eq
      obtain ⟨rfl, hext⟩ := eq
      simp only [ZFSet.ext_iff, mem_sep, and_congr_right_iff] at hext
      ext1 z
      constructor <;> intro hz
      · obtain ⟨a, ha, b, hb, rfl⟩ := (mem_funs.mp hfX).1 hz |> mem_prod.mp
        specialize hext a ha
        rw [ZFBool.mem_𝔹_iff] at hb
        obtain rfl | rfl := hb
        · have : a.pair zftrue ∉ fX := by
            intro contr
            rw [mem_funs] at hfX
            nomatch zftrue_ne_zffalse <| hfX.2 a ha |>.unique contr hz
          rw [iff_false_left this] at hext
          rw [mem_funs] at hfY
          obtain ⟨b', ab', _⟩ := hfY.2 a ha
          obtain rfl | rfl := hfY.1 ab' |> pair_mem_prod.mp |>.2 |> (ZFBool.mem_𝔹_iff b').mp
          · exact ab'
          · contradiction
        · exact hext.mp hz
      · obtain ⟨a, ha, b, hb, rfl⟩ := (mem_funs.mp hfY).1 hz |> mem_prod.mp
        specialize hext a ha
        rw [ZFBool.mem_𝔹_iff] at hb
        obtain rfl | rfl := hb
        · have : a.pair zftrue ∉ fY := by
            intro contr
            rw [mem_funs] at hfY
            nomatch zftrue_ne_zffalse <| hfY.2 a ha |>.unique contr hz
          rw [iff_false_right this] at hext
          rw [mem_funs] at hfX
          obtain ⟨b', ab', _⟩ := hfX.2 a ha
          obtain rfl | rfl := hfX.1 ab' |> pair_mem_prod.mp |>.2 |> (ZFBool.mem_𝔹_iff b').mp
          · exact ab'
          · contradiction
        · exact hext.mpr hz
    · intro X hX
      rw [mem_powerset] at hX
      let fX := A.prod 𝔹 |>.sep fun ab ↦ ab.π₁ ∈ X ↔ ab.π₂ = zftrue
      use fX
      have fX_mem_funs : fX ∈ A.funs 𝔹 := by
        rw [mem_funs]
        and_intros
        · intro z hz
          rw [mem_sep, mem_prod] at hz
          obtain ⟨⟨a, ha, b, hb, rfl⟩, _⟩ := hz
          rw [pair_mem_prod]
          exact ⟨ha, hb⟩
        · intro a ha
          by_cases a_mem_X : a ∈ X
          · use zftrue
            and_intros
            · beta_reduce
              rw [mem_sep, pair_mem_prod]
              and_intros
              · exact ha
              · rw [ZFBool.mem_𝔹_iff]
                right
                rfl
              · rwa [π₁_pair, π₂_pair, iff_true_right rfl]
            · intro b hb
              rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair] at hb
              rwa [←hb.2]
          · use zffalse
            and_intros
            · beta_reduce
              rw [mem_sep, pair_mem_prod]
              and_intros
              · exact ha
              · rw [ZFBool.mem_𝔹_iff]
                left
                rfl
              · rwa [π₁_pair, π₂_pair, iff_false_right zftrue_ne_zffalse.symm]
            · intro b hb
              rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair, ←not_iff_not] at hb
              exact Or.resolve_right (ZFBool.mem_𝔹_iff b |>.mp hb.1.2) (hb.2.mp a_mem_X)
      and_intros
      · exact fX_mem_funs
      · rw [lambda_spec]
        and_intros
        · exact fX_mem_funs
        · rwa [mem_powerset]
        · ext1 z
          rw [mem_sep, mem_sep, pair_mem_prod, π₁_pair, π₂_pair, iff_true_right rfl]
          constructor
          · intro hz
            exact ⟨hX hz, ⟨hX hz, ZFBool.zftrue_mem_𝔹⟩, hz⟩
          · rintro ⟨_, _, hz⟩
            exact hz
  · and_intros
    · intro z hz
      rw [mem_lambda] at hz
      obtain ⟨fX, X, rfl, fX_def, _, rfl⟩ := hz
      rw [pair_mem_prod]
      and_intros <;> assumption
    · intro fX fX_mem
      use A.sep fun z ↦ z.pair zftrue ∈ fX, ?_
      · intro y hy
        unfold f at hy
        rw [lambda_spec] at hy
        exact hy.2.2
      · beta_reduce
        rw [lambda_spec]
        and_intros
        · exact fX_mem
        · rw [mem_powerset]
          exact sep_subset_self
        · rfl

theorem ZFNat.iso_eq_iff {n m : ZFNat} : ↑n ≅ᶻ ↑m ↔ n = m where
  mp := by classical
    intro iso
    induction n generalizing m with
    | zero =>
      obtain ⟨bij, isfunc, isbij⟩ := iso
      ext z
      simp_rw [ZFNat.nat_zero_eq, notMem_empty, false_iff]
      intro contr
      obtain ⟨x, contr, _⟩ := isbij.2 z contr
      nomatch notMem_empty x contr
    | succ n ih =>
      obtain ⟨f, isfunc, bij⟩ := iso

      obtain ⟨ℓ, hℓ, ℓ_unq⟩ := isfunc.2 ↑n <| add_one_eq_succ ▸ lt_succ
      have ℓ_mem_m := isfunc.1 hℓ |> pair_mem_prod.mp |>.2

      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
        simp_rw [ZFNat.add_one_eq_succ]
        apply ZFNat.not_zero_imp_succ
        rintro rfl
        nomatch notMem_empty _ ℓ_mem_m

      rw [add_right_cancel]
      apply ih

      let f' := ZFSet.prod ↑n (↑(k+1) \ {ℓ}) |>.sep (· ∈ f)
      have : IsFunc ↑n (↑(k+1) \ {ℓ}) f' := by
        and_intros
        · exact sep_subset_self
        · intro z zn
          have : z ∈ (↑(n+1) : ZFSet) := by
            rw [add_one_eq_succ, ZFNat.succ, mem_insert_iff]
            right
            exact zn
          obtain ⟨y, hy, y_unq⟩ := isfunc.2 z this
          use y
          and_intros <;> beta_reduce
          · rw [mem_sep, pair_mem_prod]
            and_intros
            · exact zn
            · rw [mem_diff, mem_singleton]
              and_intros
              · exact isfunc.1 hy |> pair_mem_prod.mp |>.2
              · rintro ⟨⟩
                rw [bij.1 ↑n z ℓ _ this ℓ_mem_m hℓ hy] at zn
                · nomatch mem_irrefl _ zn
                · rw [add_one_eq_succ]
                  exact lt_succ
            · exact hy
          · intro w hzw
            rw [mem_sep, pair_mem_prod, mem_diff, mem_singleton] at hzw
            exact y_unq w hzw.2
      have bij' : IsBijective f' this := by
        rw [bijective_exists1_iff]
        intro y hy
        rw [mem_diff, add_one_eq_succ, mem_singleton, succ, mem_insert_iff] at hy
        obtain ⟨rfl | y_mem_k, y_ne_ℓ⟩ := hy
        · rw [bijective_exists1_iff] at bij
          have := bij k ?_
          · obtain ⟨x, ⟨x_mem_succ_n, x_k_f⟩, x_unq⟩ := this
            use x
            rw [add_one_eq_succ, succ, mem_insert_iff] at x_mem_succ_n
            rcases x_mem_succ_n with rfl | x_mem_n
            · nomatch y_ne_ℓ <| isfunc.2 _ (by
                rw [add_one_eq_succ]; exact lt_succ) |>.unique x_k_f hℓ
            · and_intros <;> beta_reduce
              · exact x_mem_n
              · rw [mem_sep, pair_mem_prod, mem_diff, mem_singleton]
                and_intros
                · exact x_mem_n
                · rw [add_one_eq_succ]
                  exact lt_succ
                · exact y_ne_ℓ
                · exact x_k_f
              · rintro y ⟨yn, y_k_f⟩
                rw [mem_sep, pair_mem_prod, mem_diff, mem_singleton] at y_k_f
                apply bij k (by rw [add_one_eq_succ]; exact lt_succ) |>.unique
                · and_intros
                  · rw [add_one_eq_succ, succ, mem_insert_iff]
                    right
                    exact y_k_f.1.1
                  · exact y_k_f.2
                · and_intros
                  · rw [add_one_eq_succ, succ, mem_insert_iff]
                    right
                    exact x_mem_n
                  · exact x_k_f
          · rw [add_one_eq_succ]
            exact lt_succ
        · rw [bijective_exists1_iff] at bij
          have := bij y ?_
          · obtain ⟨x, ⟨x_mem_succ_n, x_k_f⟩, x_unq⟩ := this
            use x
            rw [add_one_eq_succ, succ, mem_insert_iff] at x_mem_succ_n
            rcases x_mem_succ_n with rfl | x_mem_n
            · nomatch y_ne_ℓ <| isfunc.2 _ (by
                rw [add_one_eq_succ]; exact lt_succ) |>.unique x_k_f hℓ
            · and_intros <;> beta_reduce
              · exact x_mem_n
              · rw [mem_sep, pair_mem_prod, mem_diff, mem_singleton]
                and_intros
                · exact x_mem_n
                · rw [add_one_eq_succ, succ, mem_insert_iff]
                  right
                  exact y_mem_k
                · exact y_ne_ℓ
                · exact x_k_f
              · rintro z ⟨zn, z_k_f⟩
                rw [mem_sep, pair_mem_prod, mem_diff, mem_singleton] at z_k_f
                apply bij y ?_ |>.unique
                · and_intros
                  · rw [add_one_eq_succ, succ, mem_insert_iff]
                    right
                    exact z_k_f.1.1
                  · exact z_k_f.2
                · and_intros
                  · rw [add_one_eq_succ, succ, mem_insert_iff]
                    right
                    exact x_mem_n
                  · exact x_k_f
                · rw [add_one_eq_succ, succ, mem_insert_iff]
                  right
                  exact y_mem_k
          · rw [add_one_eq_succ, succ, mem_insert_iff]
            right
            exact y_mem_k
      have k_iso : ↑k ≅ᶻ (↑(k+1) \ {ℓ}) := by
        let g := ZFSet.prod ↑k (↑(k+1) \ {ℓ}) |>.sep fun xy ↦
          let x := xy.π₁ -- x ∈ ↑k
          let y := xy.π₂ -- y ∈ ↑(k+1) \ {ℓ}
          if x ∈ ℓ then x = y
          else y = (insert x x)
        use g, ?_
        · and_intros
          · intro x y z hz hy hz g_xz g_yz
            dsimp [g] at g_xz g_yz
            simp only [mem_sep, mem_prod, mem_diff, mem_singleton, pair_inj,
              exists_eq_right_right', π₁_pair, π₂_pair] at g_xz g_yz
            obtain ⟨⟨mem_x_k, mem_z_succ_k, z_ne_ℓ⟩, z_eq⟩ := g_xz
            obtain ⟨⟨mem_y_k, -, -⟩, z_eq'⟩ := g_yz

            -- reason into naturals
            have z_Nat : z ∈ Nat := mem_Nat_of_mem_mem_Nat (k.succ.prop) (by
              rwa [add_one_eq_succ] at mem_z_succ_k)
            have x_Nat : x ∈ Nat := mem_Nat_of_mem_mem_Nat (k.prop) mem_x_k
            have y_Nat : y ∈ Nat := mem_Nat_of_mem_mem_Nat (k.prop) hy
            have ℓ_Nat : ℓ ∈ Nat := mem_Nat_of_mem_mem_Nat (k.succ.prop) (by
              rwa [add_one_eq_succ] at ℓ_mem_m)
            let Z : ZFNat := ⟨z, z_Nat⟩
            let X : ZFNat := ⟨x, x_Nat⟩
            let Y : ZFNat := ⟨y, y_Nat⟩
            let L : ZFNat := ⟨ℓ, ℓ_Nat⟩

            split_ifs at z_eq z_eq' with x_mem_ℓ y_mem_ℓ y_lt_ℓ
            · subst x y
              rfl
            · subst x
              have Z_eq_succ_Y : Z = Y + 1 := by
                rw [add_one_eq_succ, succ, Subtype.ext_iff]
                exact z_eq'
              change Z < L at x_mem_ℓ
              change ¬ Y < L at y_mem_ℓ
              rw [not_lt] at y_mem_ℓ
              obtain L_lt_Y | L_eq_Y := y_mem_ℓ
              · have := lt_trans x_mem_ℓ L_lt_Y
                rw [Z_eq_succ_Y] at this
                absurd this
                rw [not_lt, add_one_eq_succ]
                exact le_succ
              · rw [L_eq_Y, Z_eq_succ_Y] at x_mem_ℓ
                absurd x_mem_ℓ
                rw [not_lt, add_one_eq_succ]
                exact le_succ
            · subst y
              have Z_eq_succ_X : Z = X + 1 := by
                rw [add_one_eq_succ, succ, Subtype.ext_iff]
                exact z_eq
              change ¬ X < L at x_mem_ℓ
              change Z < L at y_lt_ℓ
              rw [not_lt] at x_mem_ℓ
              obtain L_lt_X | L_eq_X := x_mem_ℓ
              · have := lt_trans y_lt_ℓ L_lt_X
                rw [Z_eq_succ_X] at this
                absurd this
                rw [not_lt, add_one_eq_succ]
                exact le_succ
              · rw [L_eq_X, Z_eq_succ_X] at y_lt_ℓ
                absurd y_lt_ℓ
                rw [not_lt, add_one_eq_succ]
                exact le_succ
            · apply succ_inj_aux'
              rw [←z_eq, ←z_eq']
          · intro y hy

            -- reason into naturals
            have y_Nat : y ∈ Nat := by
              apply mem_Nat_of_mem_mem_Nat (k.succ.prop)
              rw [add_one_eq_succ, mem_diff] at hy
              exact hy.1
            have ℓ_Nat : ℓ ∈ Nat := mem_Nat_of_mem_mem_Nat (k.succ.prop) (by
              rwa [add_one_eq_succ] at ℓ_mem_m)
            let Y : ZFNat := ⟨y, y_Nat⟩
            let L : ZFNat := ⟨ℓ, ℓ_Nat⟩

            simp only [add_one_eq_succ, succ, mem_insert_iff, mem_diff, mem_singleton] at hy
            obtain ⟨rfl | y_mem_k, y_ne_ℓ⟩ := hy
            · have ℓ_Nat : ℓ ∈ Nat := mem_Nat_of_mem_mem_Nat (k.succ.prop) (by
                rwa [add_one_eq_succ] at ℓ_mem_m)
              let L : ZFNat := ⟨ℓ, ℓ_Nat⟩
              change L < k + 1 at ℓ_mem_m
              rw [add_one_eq_succ, ←lt_le_iff] at ℓ_mem_m
              rcases ℓ_mem_m with L_lt_k | L_eq_k
              · have := ZFNat.not_zero_imp_succ (n := k) ?_
                · obtain ⟨s, rfl⟩ := this
                  use s, lt_succ
                  unfold g
                  simp only [mem_sep, pair_mem_prod, mem_diff, mem_singleton, π₁_pair, π₂_pair]
                  and_intros
                  · exact lt_succ
                  · rw [add_one_eq_succ]
                    exact lt_succ
                  · rintro rfl
                    contradiction
                  · rw [←lt_le_iff] at L_lt_k
                    conv =>
                        enter [1]
                        change s < L
                    rcases L_lt_k with L_lt_s | rfl
                    · rw [
                        ite_cond_eq_false (h := eq_false (nomatch lt_irrefl <| lt_trans · L_lt_s))]
                      rfl
                    · rw [ite_cond_eq_false (h := eq_false lt_irrefl)]
                      rfl
                · rintro rfl
                  nomatch not_lt_zero L_lt_k
              · nomatch (Subtype.coe_ne_coe.mp y_ne_ℓ) L_eq_k.symm
            · by_cases y_lt_ℓ : y ∈ ℓ
              · change Y < L at y_lt_ℓ
                use y, y_mem_k
                dsimp [g]
                simp only [mem_sep, mem_prod, mem_diff, mem_singleton, pair_inj,
                  exists_eq_right_right', π₁_pair, π₂_pair]
                split_ifs
                · and_intros
                  · exact y_mem_k
                  · change Y < k + 1
                    trans L
                    · exact y_lt_ℓ
                    · exact ℓ_mem_m
                  · exact y_ne_ℓ
                  · trivial
                · contradiction
              · change ¬ Y < L at y_lt_ℓ
                change Y < k at y_mem_k
                rw [not_lt] at y_lt_ℓ
                rw [←ne_eq, ne_comm, ne_eq] at y_ne_ℓ

                have := ZFNat.not_zero_imp_succ (n := Y) ?_
                · obtain ⟨s, Y_eq⟩ := this
                  use s
                  and_intros
                  · change s < k
                    rw [Y_eq] at y_mem_k
                    trans s.succ
                    · exact lt_succ
                    · exact y_mem_k
                  · rw [Y_eq] at y_mem_k y_lt_ℓ
                    unfold Y at Y_eq
                    rw [succ, Subtype.ext_iff] at Y_eq
                    dsimp at Y_eq
                    subst y
                    replace y_ne_ℓ : ¬ L = s.succ := by
                      intro eq
                      unfold L at eq
                      rw [succ, Subtype.ext_iff] at eq
                      dsimp at eq
                      subst ℓ
                      nomatch y_ne_ℓ
                    rcases y_lt_ℓ with L_lt_s | L_eq_s
                    · rw [← lt_le_iff] at L_lt_s
                      rcases L_lt_s with L_lt_s | L_eq_s
                      · dsimp [g]
                        rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair]
                        and_intros
                        · change s < k
                          exact lt_of_succ_lt y_mem_k
                        · rw [mem_diff, mem_singleton]
                          and_intros
                          · change s.succ < k + 1
                            rw [add_one_eq_succ, ←succ_mono]
                            exact lt_of_succ_lt y_mem_k
                          · intro contr
                            replace contr : L = s.succ := by
                              rw [succ, Subtype.ext_iff]
                              exact contr.symm
                            contradiction
                        · conv =>
                            enter [1]
                            change s < L
                          rw [ite_cond_eq_false
                            (h := eq_false (nomatch lt_irrefl <| lt_trans · L_lt_s))]
                      · subst s
                        dsimp [g]
                        rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair]
                        and_intros
                        · change L < k
                          exact lt_of_succ_lt y_mem_k
                        · rw [mem_diff, mem_singleton]
                          and_intros
                          · change L.succ < k + 1
                            rw [add_one_eq_succ, ←succ_mono]
                            exact lt_of_succ_lt y_mem_k
                          · intro contr
                            replace contr : L = L.succ := by
                              rw [succ, Subtype.ext_iff]
                              exact contr.symm
                            contradiction
                        · conv =>
                            enter [1]
                            change L < L
                          rw [ite_cond_eq_false (h := eq_false lt_irrefl)]
                    · contradiction
                · intro eq_zero
                  have := Or.resolve_right y_lt_ℓ (Subtype.coe_ne_coe.mp y_ne_ℓ)
                  rw [eq_zero] at this
                  nomatch ZFNat.not_lt_zero this
        · dsimp [g]
          and_intros
          · exact sep_subset_self
          · intro x x_mem_k
            simp only [mem_sep, mem_prod, mem_diff, mem_singleton, pair_inj,
              exists_eq_right_right', π₁_pair, π₂_pair]
            split_ifs with x_mem_ℓ
            · use x
              and_intros <;> beta_reduce
              · exact x_mem_k
              · rw [add_one_eq_succ, succ, mem_insert_iff]
                right
                exact x_mem_k
              · rintro rfl
                nomatch mem_irrefl _ x_mem_ℓ
              · rfl
              · rintro _ ⟨_, rfl⟩
                rfl
            · use (insert x x)
              and_intros <;> beta_reduce
              · exact x_mem_k
              · rw [add_one_eq_succ, succ, mem_insert_iff]
                have hx : x ∈ Nat := mem_Nat_of_mem_mem_Nat k.prop x_mem_k
                suffices (⟨x, hx⟩ + 1 : ZFNat) = k ∨ (⟨x, hx⟩ + 1 : ZFNat) < k by
                  rcases this with rfl | h
                  · left
                    rw [add_one_eq_succ, succ]
                  · right
                    rw [add_one_eq_succ, succ] at h
                    exact h
                symm
                change (⟨x, hx⟩ + 1 : ZFNat) ≤ k
                change ⟨x, hx⟩ < k at x_mem_k
                rw [lt_le_iff, ←add_one_eq_succ, add_comm, add_comm k, add_lt_add_iff_left]
                exact x_mem_k
              · rintro rfl
                rw [mem_insert_iff, not_or] at x_mem_ℓ
                nomatch x_mem_ℓ.1 rfl
              · rfl
              · rintro _ ⟨_, rfl⟩
                rfl
      trans ↑(k+1) \ {ℓ}
      · use f', this
      · apply ZFSet.isIso_symm
        exact k_iso
  mpr := by
    rintro rfl
    apply isIso_refl

open Classical in
noncomputable def currify {A B C : ZFSet} (f : ZFSet)
  (hf : (A.prod B).IsFunc C f := by zfun) : ZFSet :=
  λᶻ : A   → (B.funs C)
       | a ↦ if ha : a ∈ A then
                λᶻ : B → C
                   | b ↦ if hb : b ∈ B then
                          @ᶻf ⟨a.pair b, by rw [is_func_dom_eq hf, pair_mem_prod]; exact ⟨ha, hb⟩⟩
                        else ∅
              else ∅

@[zfun]
theorem currify_is_func {A B C : ZFSet} (f : ZFSet)
  (hf : (A.prod B).IsFunc C f := by zfun) : A.IsFunc (B.funs C) (currify f hf) := by
  apply lambda_isFunc
  intro x hx
  rw [dite_cond_eq_true (eq_true hx), mem_funs]
  and_intros
  · exact lambda_subset
  · intro y hy
    obtain ⟨z, hz, z_unq⟩ := hf.2 (x.pair y) (by rw [pair_mem_prod]; exact ⟨hx, hy⟩)
    use z
    and_intros <;> beta_reduce
    · rw [lambda_spec]
      and_intros
      · exact hy
      · exact hf.1 hz |> pair_mem_prod.mp |>.2
      · rw [dite_cond_eq_true (eq_true hy), fapply.of_pair (is_func_is_pfunc hf) hz]
    · intro w hw
      rw [lambda_spec, dite_cond_eq_true (eq_true hy)] at hw
      rw [hw.2.2]
      apply z_unq
      apply fapply.def

open Classical in
noncomputable def uncurrify {A B C : ZFSet} (g : ZFSet)
  (hg : A.IsFunc (B.funs C) g := by zfun) : ZFSet :=
  λᶻ : (A.prod B) → C
       | ab ↦ if hab : ab ∈ A.prod B then
                let a := ab.π₁
                let b := ab.π₂
                let f := @ᶻg ⟨a, by
                    rw [is_func_dom_eq hg]
                    rw [pair_eta hab, pair_mem_prod] at hab
                    exact hab.1
                  ⟩
                have hf := mem_funs.mp f.2
                @ᶻf ⟨b, by
                    rw [is_func_dom_eq hf]
                    rw [pair_eta hab, pair_mem_prod] at hab
                    exact hab.2
                  ⟩
              else ∅

@[zfun]
theorem uncurrify_is_func {A B C : ZFSet} (g : ZFSet)
  (hg : A.IsFunc (B.funs C) g := by zfun) : (A.prod B).IsFunc C (uncurrify g hg) := by
  apply lambda_isFunc
  intro z hz
  simp only [dite_cond_eq_true (eq_true hz), SetLike.coe_mem]

@[simp]
theorem currify_of_uncurrify {A B C : ZFSet} (f : ZFSet)
    (hf : (A.IsFunc (B.funs C)) f := by zfun) :
  currify (uncurrify f) = f := by
    simp only [currify, uncurrify, lambda_eta hf]
    rw [lambda_ext_iff]
    · intro x hx
      simp_rw [dite_cond_eq_true (eq_true hx)]
      conv =>
        enter [2,1]
        change ?f_x
      rw [lambda_eta (mem_funs.mp ?f_x.2), lambda_ext_iff]
      · intro y hy
        simp_rw [dite_cond_eq_true (eq_true hy)]
        conv_lhs =>
          rw [
            fapply_lambda
              (by intro _ h; rw [dite_cond_eq_true (eq_true h)]; apply fapply_mem_range)
              (by rw [pair_mem_prod]; exact ⟨hx, hy⟩),
            dite_cond_eq_true (eq_true (by rw [pair_mem_prod]; exact ⟨hx, hy⟩))]
          simp only [π₁_pair, π₂_pair]
        congr 2
        · simp only [π₁_pair]
        · apply proof_irrel_heq
        · congr 1
          · funext x
            simp only [π₁_pair, mem_sep]
          · apply proof_irrel_heq
      · intro _ h
        rw [dite_cond_eq_true (eq_true h)]
        apply fapply_mem_range
    · intro _ hx
      rw [dite_cond_eq_true (eq_true hx)]
      apply mem_funs_of_lambda
      intro _ hx
      rw [dite_cond_eq_true (eq_true hx)]
      apply fapply_mem_range

theorem uncurrify_of_currify {A B C : ZFSet} (g : ZFSet)
    (hg : (A.prod B).IsFunc C g := by zfun) :
  uncurrify (currify g) = g := by
    simp only [currify, uncurrify, lambda_eta hg]
    rw [lambda_ext_iff]
    · intro ab hab
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.mp hab
      simp_rw [dite_cond_eq_true (eq_true hab), π₂_pair]
      conv_lhs =>
        rw [fapply_eq_Image_singleton (by rw [←mem_funs]; apply fapply_mem_range) hb]
        conv =>
          enter [1,1]
          simp only [π₁_pair]
          rw [
            fapply_lambda (by
                intro _ h
                rw [dite_cond_eq_true (eq_true h)]
                apply mem_funs_of_lambda
                intro _ hx
                rw [dite_cond_eq_true (eq_true hx)]
                apply fapply_mem_range
              ) ha,
            dite_cond_eq_true (eq_true ha)]
        rw [←fapply_eq_Image_singleton (lambda_isFunc (fun h ↦ by
              rw [dite_cond_eq_true (eq_true h)]
              apply fapply_mem_range)) hb,
          fapply_lambda (fun h ↦ by rw [dite_cond_eq_true (eq_true h)]; apply fapply_mem_range) hb,
          dite_cond_eq_true (eq_true hb)]
    · intro _ h
      rw [dite_cond_eq_true (eq_true h)]
      apply fapply_mem_range

open Classical in
theorem isIso_curry {A B C : ZFSet} :
  (A.prod B).funs C ≅ᶻ A.funs (B.funs C) := by
  let curry  := λᶻ : (A.prod B).funs C → A.funs (B.funs C)
    | f ↦ if hf : f ∈ (A.prod B).funs C then
            currify f (mem_funs.mp hf)
          else ∅
  let uncurry := λᶻ : A.funs (B.funs C) → (A.prod B).funs C
    | g ↦ if hg : g ∈ A.funs (B.funs C) then
            uncurrify g (mem_funs.mp hg)
          else ∅
  have hcurry : IsFunc ((A.prod B).funs C) (A.funs (B.funs C)) curry := by
    apply lambda_isFunc
    intro f hf
    rw [dite_cond_eq_true (eq_true hf), mem_funs]
    apply currify_is_func
  have huncurry : IsFunc (A.funs (B.funs C)) ((A.prod B).funs C) uncurry := by
    apply lambda_isFunc
    intro g hg
    rw [dite_cond_eq_true (eq_true hg), mem_funs]
    apply uncurrify_is_func

  have l_inv : (uncurry ∘ᶻ curry) = 𝟙((A.prod B).funs C) := by
    rw [is_func_ext_iff (IsFunc_of_composition_IsFunc huncurry hcurry) Id.IsFunc]
    intro f hf
    rw [←SetLike.coe_eq_coe, fapply_Id hf]
    conv_lhs =>
      rw [fapply_composition huncurry hcurry hf]
      unfold uncurry
      rw [
        fapply_lambda (by
            intro _ h
            rw [dite_cond_eq_true (eq_true h), mem_funs]
            apply uncurrify_is_func
          ) (fapply_mem_range _ _),
        dite_cond_eq_true (eq_true (fapply_mem_range _ _))]
      conv =>
        enter [1]
        unfold curry
        rw [
          fapply_lambda (by
              intro _ h
              rw [dite_cond_eq_true (eq_true h), mem_funs]
              apply currify_is_func
            ) hf,
          dite_cond_eq_true (eq_true hf)]
      rw [uncurrify_of_currify f (mem_funs.mp hf)]

  have r_inv : (curry ∘ᶻ uncurry) = 𝟙(A.funs (B.funs C)) := by
    rw [is_func_ext_iff (IsFunc_of_composition_IsFunc hcurry huncurry) Id.IsFunc]
    intro g hg
    rw [←SetLike.coe_eq_coe, fapply_Id hg]
    conv_lhs =>
      rw [fapply_composition hcurry huncurry hg]
      unfold curry
      rw [
        fapply_lambda (by
            intro _ h
            rw [dite_cond_eq_true (eq_true h), mem_funs]
            apply currify_is_func
          ) (fapply_mem_range _ _),
        dite_cond_eq_true (eq_true (fapply_mem_range _ _))]
      conv =>
        enter [1]
        unfold uncurry
        rw [
          fapply_lambda (by
              intro _ h
              rw [dite_cond_eq_true (eq_true h), mem_funs]
              apply uncurrify_is_func
            ) hg,
          dite_cond_eq_true (eq_true hg)]
      rw [currify_of_uncurrify g (mem_funs.mp hg)]

  exact isIso_of_two_sided_inverse l_inv r_inv

end Lemmas

end Isomorphisms

end ZFSet
