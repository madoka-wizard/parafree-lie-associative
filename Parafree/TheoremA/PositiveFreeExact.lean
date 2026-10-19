import Parafree.TheoremA.PositiveFreeMap
import Parafree.Linear.DFinsuppScalar

/-! The positive free map has precisely the scalar-reduction kernel and fills
all positive components of the actual reduced grading. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie Parafree.Linear
open Auxiliary

/-- The zero-degree component of the free map vanishes. -/
theorem freeGradedLinear_zero (x : RelationFree) : freeGradedLinear x 0 = 0 := by
  refine FreeHomogeneous.homogeneous_induction RelationBasisIndex
    (fun x => freeGradedLinear x 0 = 0) ?_ ?_ ?_ x
  · change freeGradedLinear 0 0 = 0
    rw [map_zero]; rfl
  · intro a b ha hb
    rw [map_add, DFinsupp.add_apply, ha, hb, add_zero]
  · intro n a
    rw [freeGradedLinear_homogeneous, homogeneousGradedMap_succ]
    exact DFinsupp.single_eq_of_ne (Nat.zero_ne_add_one n)

/-- Componentwise formula for the map on an arbitrary, finite sum. -/
theorem freeGradedLinear_component (n : ℕ) (x : RelationFree) :
    freeGradedLinear x (n + 1) = positiveLayerEquiv n
      (ModScalar.mk (2 : ℤ) _ ((FreeHomogeneous.sumEquiv RelationBasisIndex).symm x (n + 1))) := by
  have h : (DFinsupp.lapply (n + 1)).comp (DFinsupp.lsum ℤ homogeneousGradedMap) =
      (positiveLayerEquiv n).toLinearMap.comp
        ((ModScalar.mk (2 : ℤ) (RelationComponent (n + 1))).comp (DFinsupp.lapply (n + 1))) := by
    apply DFinsupp.lhom_ext
    intro m a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, DFinsupp.lsum_single, DFinsupp.lapply_apply]
    change homogeneousGradedMap m a (n + 1) = positiveLayerEquiv n
      (ModScalar.mk (2 : ℤ) _ ((DFinsupp.single m a : FreeHomogeneous.Components RelationBasisIndex) (n + 1)))
    cases m with
    | zero =>
      change (0 : ReducedGraded) (n + 1) = _
      rw [DFinsupp.single_eq_of_ne (Nat.succ_ne_zero n), map_zero, map_zero]
      rfl
    | succ m =>
      rw [homogeneousGradedMap_succ]
      unfold gradedClass
      by_cases he : n = m
      · subst m
        simp only [DFinsupp.single_eq_same, positiveLayerEquiv_mk]
      · have hne : n + 1 ≠ m + 1 := by omega
        simp only [DFinsupp.single_eq_of_ne hne, map_zero]
  exact LinearMap.congr_fun h ((FreeHomogeneous.sumEquiv RelationBasisIndex).symm x)

/-- No relation is lost when the free source is mapped into the actual grading. -/
theorem freeGradedLinear_eq_zero_iff (x : RelationFree) :
    freeGradedLinear x = 0 ↔ ∃ y : RelationFree, (2 : ℤ) • y = x := by
  constructor
  · intro hx
    let a := (FreeHomogeneous.sumEquiv RelationBasisIndex).symm x
    have ha : ∀ n, ∃ b : RelationComponent n, (2 : ℤ) • b = a n := by
      intro n
      cases n with
      | zero =>
        refine ⟨0, ?_⟩
        rw [smul_zero]
        exact (Subtype.ext (FreeHomogeneous.component_zero RelationBasisIndex (a 0))).symm
      | succ n =>
        apply (ModScalar.mk_eq_zero (2 : ℤ) _ _).mp
        apply (positiveLayerEquiv n).injective
        rw [map_zero, ← freeGradedLinear_component, hx]
        rfl
    obtain ⟨b, hb⟩ := (dfinsupp_exists_smul_iff (2 : ℤ) a).mpr ha
    refine ⟨FreeHomogeneous.sumEquiv RelationBasisIndex b, ?_⟩
    rw [← map_smul, hb]
    exact (FreeHomogeneous.sumEquiv RelationBasisIndex).apply_symm_apply x
  · rintro ⟨y, rfl⟩
    rw [map_smul]
    exact reducedGraded_two_nsmul (freeGradedLinear y)

/-- Every single positive homogeneous class has a free preimage. -/
theorem positiveSingle_mem_range (n : ℕ) (a : ReducedLayer (n + 1)) :
    DFinsupp.single (n + 1) a ∈ LinearMap.range freeGradedLinear := by
  obtain ⟨b, rfl⟩ := (positiveLayerEquiv n).surjective a
  obtain ⟨c, rfl⟩ := ModScalar.mk_surjective (2 : ℤ) _ b
  refine ⟨c, ?_⟩
  rw [freeGradedLinear_homogeneous, homogeneousGradedMap_succ, positiveLayerEquiv_mk]
  rfl

/-- The exact image is the positive part of the actual grading. -/
theorem freeGradedLinear_range_iff (x : ReducedGraded) :
    x ∈ LinearMap.range freeGradedLinear ↔ x 0 = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact freeGradedLinear_zero a
  · intro hx
    have h : ∀ y : ReducedGraded, y - DFinsupp.single 0 (y 0) ∈
        LinearMap.range freeGradedLinear := by
      intro y
      induction y using DFinsupp.induction with
      | h0 => simp only [DFinsupp.zero_apply, DFinsupp.single_zero, sub_self,
          Submodule.zero_mem]
      | @ha n a b _ _ ih =>
        have hs : DFinsupp.single n a - DFinsupp.single 0 ((DFinsupp.single n a) 0) ∈
            LinearMap.range freeGradedLinear := by
          cases n with
          | zero => rw [DFinsupp.single_eq_same, sub_self]; exact Submodule.zero_mem _
          | succ n =>
            rw [DFinsupp.single_eq_of_ne (Nat.zero_ne_add_one n), DFinsupp.single_zero, sub_zero]
            exact positiveSingle_mem_range n a
        have ht := (LinearMap.range freeGradedLinear).add_mem hs ih
        simpa only [DFinsupp.add_apply, DFinsupp.single_add, add_sub_add_comm] using ht
    simpa only [hx, DFinsupp.single_zero, sub_zero] using h x

end Parafree.TheoremA.RationalModel
