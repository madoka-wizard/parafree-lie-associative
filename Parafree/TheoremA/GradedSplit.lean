import Parafree.TheoremA.PositiveFree

/-! The actual grading is split by the Lie projection onto degree zero.
Its kernel is the free positive ideal identified in `PositiveFree`. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie
open Auxiliary (dividedFiltration)

/-- Additive induction on integral homogeneous representatives of the reduction. -/
theorem graded_induction (P : ReducedGraded → Prop) (hzero : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hclass : ∀ n (a : dividedFiltration n), P (gradedClass n a))
    (x : ReducedGraded) : P x := by
  induction x using DFinsupp.induction with
  | h0 => exact hzero
  | @ha n a x _ _ ih =>
    apply hadd _ _ _ ih
    obtain ⟨b, rfl⟩ := (reducedLayerRelations n).mkQ_surjective a
    exact hclass n b

def zeroProjection : ReducedGraded →ₗ[ℤ] ReducedGraded :=
  (DFinsupp.lsingle 0).comp (DFinsupp.lapply 0)

@[simp] theorem zeroProjection_apply (x : ReducedGraded) :
    zeroProjection x = DFinsupp.single 0 (x 0) := rfl

@[simp] theorem zeroProjection_class_zero (a : dividedFiltration 0) :
    zeroProjection (gradedClass 0 a) = gradedClass 0 a := by
  simp only [zeroProjection_apply, gradedClass, DFinsupp.single_eq_same]

theorem zeroProjection_class_of_ne (n : ℕ) (hn : n ≠ 0) (a : dividedFiltration n) :
    zeroProjection (gradedClass n a) = 0 := by
  simp only [zeroProjection_apply, gradedClass, DFinsupp.single_eq_of_ne hn.symm,
    DFinsupp.single_zero]

theorem zeroProjection_lie_class (i j : ℕ)
    (a : dividedFiltration i) (b : dividedFiltration j) :
    zeroProjection ⁅gradedClass i a, gradedClass j b⁆ =
      ⁅zeroProjection (gradedClass i a), zeroProjection (gradedClass j b)⁆ := by
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      rw [gradedClass_lie, zeroProjection_class_zero,
        zeroProjection_class_zero, zeroProjection_class_zero, gradedClass_lie]
    · rw [gradedClass_lie, zeroProjection_class_of_ne _ (by omega),
        zeroProjection_class_of_ne j hj, lie_zero]
  · rw [gradedClass_lie, zeroProjection_class_of_ne _ (by omega),
      zeroProjection_class_of_ne i hi, zero_lie]

theorem zeroProjection_lie (x y : ReducedGraded) :
    zeroProjection ⁅x, y⁆ = ⁅zeroProjection x, zeroProjection y⁆ := by
  refine graded_induction
    (fun x => zeroProjection ⁅x, y⁆ = ⁅zeroProjection x, zeroProjection y⁆) ?_ ?_ ?_ x
  · simp only [zero_lie, map_zero]
  · intro a b ha hb
    simp only [add_lie, map_add, ha, hb]
  · intro i a
    refine graded_induction
      (fun y => zeroProjection ⁅gradedClass i a, y⁆ =
        ⁅zeroProjection (gradedClass i a), zeroProjection y⁆) ?_ ?_ ?_ y
    · simp only [lie_zero, map_zero]
    · intro b c hb hc
      simp only [lie_add, map_add, hb, hc]
    · intro j b
      exact zeroProjection_lie_class i j a b

/-- The actual field-linear Lie projection, rather than just a decomposition
of the underlying vector space. -/
def zeroProjectionHom : ReducedGraded →ₗ⁅ZMod 2⁆ ReducedGraded :=
  { zeroProjection.toAddMonoidHom.toZModLinearMap 2 with map_lie' := zeroProjection_lie _ _ }

theorem zeroProjection_idempotent (x : ReducedGraded) :
    zeroProjectionHom (zeroProjectionHom x) = zeroProjectionHom x := by
  change DFinsupp.single 0 ((DFinsupp.single 0 (x 0) : ReducedGraded) 0) = _
  rw [DFinsupp.single_eq_same]
  rfl

def positiveIdeal : LieIdeal (ZMod 2) ReducedGraded := zeroProjectionHom.ker

theorem mem_positiveIdeal (x : ReducedGraded) : x ∈ positiveIdeal ↔ x 0 = 0 := by
  change (DFinsupp.single 0 (x 0) : ReducedGraded) = 0 ↔ x 0 = 0
  constructor
  · intro h
    have he := congrArg (fun a : ReducedGraded => a 0) h
    simpa only [DFinsupp.single_eq_same, DFinsupp.zero_apply] using he
  · intro h
    rw [h, DFinsupp.single_zero]

/-- The intrinsic positive ideal and the proved free image are the same Lie algebra. -/
def positiveIdealEquiv : PositiveAlgebra ≃ₗ⁅ZMod 2⁆ positiveIdeal where
  toFun x := ⟨x, (mem_positiveIdeal x).mpr ((fieldFreeHom_range_iff x).mp x.property)⟩
  invFun x := ⟨x, (fieldFreeHom_range_iff x).mpr ((mem_positiveIdeal x).mp x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

def freePositiveIdealEquiv : FieldRelationFree ≃ₗ⁅ZMod 2⁆ positiveIdeal :=
  positiveFreeEquiv.trans positiveIdealEquiv

theorem positiveIdealHomologyTwo_subsingleton :
    Subsingleton (LieRings.Homological.LieHomology.Homology
      (R := ZMod 2) (L := positiveIdeal) 2) := by
  letI := positiveHomologyTwo_subsingleton
  exact (Parafree.Homology.lieEquivHomology positiveIdealEquiv 2).symm.injective.subsingleton

/-- Every element splits into a degree-zero part and an element of the free ideal. -/
theorem sub_zeroProjection_mem (x : ReducedGraded) :
    x - zeroProjectionHom x ∈ positiveIdeal := by
  change zeroProjectionHom (x - zeroProjectionHom x) = 0
  rw [map_sub, zeroProjection_idempotent, sub_self]

end Parafree.TheoremA.RationalModel
