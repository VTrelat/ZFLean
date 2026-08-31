module

public import Mathlib.SetTheory.ZFC.Basic
public import ZFLean.Def
import ZFLean.Tactics
public import ZFLean.Functions

public section

namespace ZFSet

open Classical in
def equivZFRelation (E : ZFSet) : Equiv { R : ZFSet // R ⊆ E.prod E } (E → E → Prop) where
  toFun R := fun x y => x.val.pair y.val ∈ R.val
  invFun r := ⟨E.prod E |>.sep  fun p => if h : p ∈ E.prod E then
      r
      ⟨p.π₁, by
        rw [mem_prod] at h
        obtain ⟨x, hx, y, hy, rfl⟩ := h
        rw [π₁_pair]
        exact hx
      ⟩
      ⟨p.π₂, by
        rw [mem_prod] at h
        obtain ⟨x, hx, y, hy, rfl⟩ := h
        rw [π₂_pair]
        exact hy
      ⟩
    else False,
    sep_subset⟩
  left_inv R := by
    ext p
    dsimp only
    rw [mem_sep, ←exists_prop]
    conv => enter [1, 1, h] ; rw [dif_pos h]
    rw [mem_prod, exists_prop, ←exists_and_right]
    conv =>
      enter [1, 1, x]
      rw [and_assoc, ←exists_and_right]
      conv =>
        enter [2, 1, y]
        rw [and_assoc]
        conv =>
          right
          rw [←exists_prop]
          conv => enter [1, h] ; rw [h, π₁_pair, π₂_pair, ←h]
          rw [exists_prop]
        rw [←and_assoc]
      rw [exists_and_right, ←and_assoc]
    rw [exists_and_right, ←mem_prod, and_iff_right_of_imp (R.prop ·)]
  right_inv r := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    dsimp only
    rw [mem_sep, ←exists_prop]
    conv =>
      enter [1, 1, h]
      rw [dif_pos h]
      conv =>
        congr <;> left
        · rw [π₁_pair]
        · rw [π₂_pair]
      change r ⟨x, hx⟩ ⟨y, hy⟩
    rw [exists_prop, pair_mem_prod, and_iff_right ⟨hx, hy⟩]

instance (E : ZFSet) : TransferEquiv { R : ZFSet // R ⊆ E.prod E } (E → E → Prop) where
  equiv := E.equivZFRelation

theorem equivZFRelation_related (E : ZFSet) (R : { R : ZFSet // R ⊆ E.prod E }) (x y : E) :
    E.equivZFRelation R x y = (x.val.pair y.val ∈ R.val) := by
  unfold equivZFRelation
  dsimp

theorem equivZFRelation_Reflexivity (E : ZFSet) (R : { R : ZFSet // R ⊆ E.prod E }) :
    (∀ x, E.equivZFRelation R x x) = is_rel_reflexive R.val R.prop := by
  conv =>
    rw [is_rel_reflexive_iff]
    left
    conv => ext x ; rw [equivZFRelation_related]
    rw [Subtype.forall]

theorem equivZFRelation_Symmetry (E : ZFSet) (R : { R : ZFSet // R ⊆ E.prod E }) :
    (∀ x y, E.equivZFRelation R x y → E.equivZFRelation R y x) = is_rel_symmetric R.val R.prop := by
  conv =>
    rw [is_rel_symmetric_iff _ R.prop]
    left
    conv => enter [x, y] ; rw [equivZFRelation_related, equivZFRelation_related]
    repeat rw [Subtype.forall] ; ext v ; (conv => repeat rw [forall_comm] ; ext _)
    dsimp only
    rw [←and_imp, ←pair_mem_prod, ←and_imp, and_iff_right_of_imp (R.prop ·)]
  ext
  constructor
  · intro h x y
    exact ⟨(h x y ·), (h y x ·)⟩
  · intro h x y
    exact Iff.mp <| h x y

theorem equivZFRelation_Transitivity (E : ZFSet) (R : { R : ZFSet // R ⊆ E.prod E }) :
    (∀ x y z, E.equivZFRelation R x y → E.equivZFRelation R y z → E.equivZFRelation R x z)
      = is_rel_transitive R.val R.prop := by
  conv =>
    rw [is_rel_transitive_iff _ R.prop]
    left
    conv =>
      enter [_, _, _]
      rw [equivZFRelation_related, equivZFRelation_related, equivZFRelation_related]
    repeat
      rw [Subtype.forall]
      ext x
      conv => repeat
        rw [forall_comm]
        ext h
        conv => pattern (occs := *) _ → _ → _
    dsimp only
    rw [←and_imp, ←and_imp, and_assoc, ←and_imp, ←and_imp, and_assoc]
    left
    conv =>
      left
      conv => enter [2, 1] ; rw [←and_self (_ ∈ E)]
      rw [and_assoc, ←pair_mem_prod, ←and_assoc, ←pair_mem_prod]
    rw [and_iff_right_of_imp fun ⟨l,r⟩ => ⟨R.prop l, R.prop r⟩]

theorem equivZFRelation_Equivalence (E : ZFSet) (R : { R : ZFSet // R ⊆ E.prod E }) :
    Equivalence (E.equivZFRelation R) = is_rel_equivalence R.val R.prop := by
  ext
  rw [is_rel_equivalence, ←equivZFRelation_Reflexivity, ←equivZFRelation_Symmetry,
    ←equivZFRelation_Transitivity]
  constructor <;> intro ⟨r, s, t⟩ <;> [split_ands ; constructor] <;> assumption

theorem ZFEquiv_of_Equivalence (E : ZFSet) (r : E → E → Prop) (re : Equivalence r) :
    (E.equivZFRelation.symm r).val.is_rel_equivalence (E.equivZFRelation.symm r).prop :=
  (equivZFRelation_Equivalence E (E.equivZFRelation.symm r)).mp
    ( by rw [@Equiv.apply_symm_apply] ; exact re)

@[expose]
def ZFQuotient (E R : ZFSet) : ZFSet :=
  E.powerset.sep (fun c => ∃ x ∈ c, ∀ y : ZFSet, y ∈ c ↔ x.pair y ∈ R)

namespace ZFQuotient

variable
  {E R : ZFSet}


def class_of (hrR : R ⊆ E.prod E := by zrel)
  (heR : R.is_rel_equivalence hrR := by assumption) (x : E) :
    E.ZFQuotient R :=
  ⟨E.sep fun y => x.val.pair y ∈ R, by
    rw [ZFQuotient, mem_sep, mem_powerset]
    exists sep_subset, x
    rw [mem_sep]
    rw [is_rel_equivalence, R.is_rel_reflexive_iff hrR, R.is_rel_symmetric_iff hrR] at heR
    exists ⟨x.prop, heR.left x x.prop⟩
    intro y
    rw [mem_sep, and_iff_right_of_imp (And.right <| pair_mem_prod.mp <| hrR ·)]
  ⟩

theorem mem_class_of_self (hrR : R ⊆ E.prod E := by zrel)
  (heR : R.is_rel_equivalence hrR := by assumption) (x : E) :
    x.val ∈ (class_of hrR heR x).val := by
  rw [class_of, mem_sep]
  constructor
  · exact x.prop
  · rw [is_rel_equivalence, R.is_rel_reflexive_iff] at heR
    exact heR.left x x.prop

theorem mem_class_of_iff_related (hrR : R ⊆ E.prod E := by zrel)
  (heR : R.is_rel_equivalence hrR := by assumption) (x : E) (y : ZFSet) :
    y ∈ (class_of hrR heR x).val ↔ y.pair x.val ∈ R := by
  rw [class_of, mem_sep, and_iff_right_of_imp (And.right <| pair_mem_prod.mp <| hrR ·)]
  rw [is_rel_equivalence, R.is_rel_symmetric_iff hrR] at heR
  exact heR.right.left x y


def of_in_class {C : E.ZFQuotient R} (w : C.val) : E :=
  ⟨w |>.val, (mem_powerset.mp <| And.left <| mem_sep.mp C.prop) w.prop⟩

theorem class_of_mem_eq_self (hrR : R ⊆ E.prod E := by zrel)
  (heR : R.is_rel_equivalence hrR := by assumption) (C : E.ZFQuotient R) (x : C.val) :
    class_of hrR heR (of_in_class x) = C := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨C, hC⟩ := C
  obtain ⟨hC', ⟨z,hz,extC⟩⟩ := mem_sep.mp hC
  rw [of_in_class, class_of]
  ext y
  dsimp only
  rw [mem_sep, and_iff_right_of_imp (And.right <| pair_mem_prod.mp <| hrR ·)]
  rw [extC]
  rw [is_rel_equivalence, R.is_rel_transitive_iff, R.is_rel_symmetric_iff] at heR
  let ⟨r, s, t⟩ := heR
  constructor
  · intro xy_related
    exact t z x y ⟨(extC x |>.mp hx), xy_related⟩
  · intro zy_related
    exact t x z y ⟨s z x |>.mp (extC x |>.mp hx), zy_related⟩

theorem class_eq_iff_related (hrR : R ⊆ E.prod E := by zrel)
  (heR : R.is_rel_equivalence hrR := by assumption) (x y : E) :
    class_of hrR heR x = class_of hrR heR y ↔ x.val.pair y.val ∈ R := by
  constructor
  · intro h
    rw [←mem_class_of_iff_related hrR heR, ←h]
    exact mem_class_of_self hrR heR x
  · intro xy_related
    obtain ⟨x, x_E⟩ := x
    rw [←mem_class_of_iff_related hrR heR] at xy_related
    change class_of _ _ (of_in_class ⟨x, xy_related⟩) = _
    rw [class_of_mem_eq_self hrR heR]

@[expose]
noncomputable def choose_repr (C : E.ZFQuotient R) : C.val :=
    let hC := mem_sep.mp C.prop
    ⟨hC.right.choose, hC.right.choose_spec.left⟩

noncomputable def lift
    (f : E → α) (C : E.ZFQuotient R) : α :=
  (f (of_in_class (choose_repr C)))

theorem lift_class_of (hrR : R ⊆ E.prod E := by zrel)
(heR : R.is_rel_equivalence hrR := by assumption) (f : E → α)
(h : ∀ a b, a.val.pair b.val ∈ R → f a = f b) (x : E) :
    lift f (class_of hrR heR x) = f x := by
  apply h
  rw [of_in_class, ←mem_class_of_iff_related hrR heR]
  exact Subtype.prop <| choose_repr <| class_of _ _ x

@[expose]
def toSetoid {E R : ZFSet}
    (hrR : R ⊆ E.prod E := by zrel)
    (heR : R.is_rel_equivalence hrR := by assumption) : Setoid E where
  r :=  E.equivZFRelation ⟨R, hrR⟩
  iseqv := E.equivZFRelation_Equivalence ⟨R, hrR⟩ |>.mpr heR



noncomputable def equivZFQuotient (hrR : R ⊆ E.prod E := by zrel)
  (heR : R.is_rel_equivalence hrR := by assumption) :
    Equiv (ZFQuotient E R) (Quotient <| toSetoid  hrR heR) where
  toFun C := lift (fun x => ⟦x⟧) C
  invFun W := Quotient.liftOn W (fun W => class_of hrR heR W) (by
    intro a b related
    change a.val.pair b.val ∈ R at related
    exact (class_eq_iff_related hrR heR a b).mpr related
    )
  left_inv := by
    intro C
    dsimp only
    let W := choose_repr C
    rw [←class_of_mem_eq_self hrR heR C, lift_class_of _ _ _ _ (of_in_class W),Quotient.liftOn_mk]
    intro a b related
    rw [Quotient.eq]
    exact related
  right_inv := by
    intro W
    cases W using Quotient.ind
    rename_i W
    dsimp only
    generalize_proofs h
    rw [Quotient.liftOn_mk, lift_class_of _ _ _]
    intro a b related
    rw [Quotient.eq]
    exact related

noncomputable def equivZFQuotient_of_rel {r : E → E → Prop} (re : Equivalence r) :
    Equiv (E.ZFQuotient <| E.equivZFRelation.symm r) (Quotient ⟨r,re⟩) :=
  Equiv.trans
    (
      equivZFQuotient _
        <| (equivZFRelation_Equivalence E (E.equivZFRelation.symm r)).mp
          ( by rw [@Equiv.apply_symm_apply] ; exact re)
    )
    ( by
      apply Quotient.congrRight
      unfold toSetoid
      dsimp only
      rw [Subtype.eta, E.equivZFRelation.apply_symm_apply]
      intro _ _
      rfl
    )

@[expose]
noncomputable def equivZFProdProd {E F : ZFSet} : Equiv (E.prod F) (E × F) where
  toFun p := (
    ⟨p.val.π₁, by obtain ⟨_,_,_,_,hp⟩ := mem_prod.mp p.prop ; rwa [hp, π₁_pair]⟩,
    ⟨p.val.π₂, by obtain ⟨_,_,_,_,hp⟩ := mem_prod.mp p.prop ; rwa [hp, π₂_pair]⟩
  )
  invFun p := ⟨p.1.val.pair p.2.val, pair_mem_prod.mpr <| ⟨p.1.prop, p.2.prop⟩⟩
  left_inv p := by
    obtain ⟨x,hx,y,hy,hp⟩ := mem_prod.mp p.prop
    simp_rw [Subtype.ext_iff, hp, π₁_pair, π₂_pair]
  right_inv p := by
    dsimp only
    simp_rw [Prod.ext_iff,Subtype.ext_iff, π₁_pair, π₂_pair]
    trivial

end ZFQuotient

end ZFSet

end
