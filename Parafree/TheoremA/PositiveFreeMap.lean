import Parafree.TheoremA.PositiveLayers
import Parafree.TheoremA.GradedModel

/-! The concrete free relation map into the positive grading. Preservation of
the bracket is checked on homogeneous representatives and extended additively. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie Parafree.Linear
open Auxiliary

abbrev RelationComponent (n : ℕ) := FreeHomogeneous.component RelationBasisIndex n

def homogeneousGradedMap : (n : ℕ) → RelationComponent n →ₗ[ℤ] ReducedGraded
  | 0 => 0
  | n + 1 => (DFinsupp.lsingle (n + 1)).comp
      ((reducedLayerRelations (n + 1)).mkQ.comp (homogeneousRelationTerm n))

@[simp] theorem homogeneousGradedMap_succ (n : ℕ) (x : RelationComponent (n + 1)) :
    homogeneousGradedMap (n + 1) x = gradedClass (n + 1) (homogeneousRelationTerm n x) := rfl

/-- Sum the specified maps on homogeneous components. -/
def freeGradedLinear : RelationFree →ₗ[ℤ] ReducedGraded :=
  (DFinsupp.lsum ℤ homogeneousGradedMap).comp
    (FreeHomogeneous.sumEquiv RelationBasisIndex).symm.toLinearMap

theorem freeGradedLinear_homogeneous (n : ℕ) (x : RelationComponent n) :
    freeGradedLinear x = homogeneousGradedMap n x := by
  change DFinsupp.lsum ℤ homogeneousGradedMap
    ((FreeHomogeneous.sumEquiv RelationBasisIndex).symm x) = _
  rw [FreeHomogeneous.sumEquiv_symm_component, DFinsupp.lsum_single]

theorem gradedClass_congr {i j : ℕ} (h : i = j)
    {a : dividedFiltration i} {b : dividedFiltration j}
    (hab : (a : Auxiliary.Free ℤ) = (b : Auxiliary.Free ℤ)) :
    gradedClass i a = gradedClass j b := by
  subst j
  exact congrArg (gradedClass i) (Subtype.ext hab)

theorem freeGradedLinear_lie_homogeneous (i j : ℕ)
    (x : RelationComponent (i + 1)) (y : RelationComponent (j + 1)) :
    freeGradedLinear ⁅(x : RelationFree), (y : RelationFree)⁆ =
      ⁅freeGradedLinear x, freeGradedLinear y⁆ := by
  let z : RelationComponent ((i + j + 1) + 1) :=
    ⟨⁅(x : RelationFree), (y : RelationFree)⁆, by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        FreeHomogeneous.component_lie RelationBasisIndex x.property y.property⟩
  change freeGradedLinear z = _
  rw [freeGradedLinear_homogeneous, freeGradedLinear_homogeneous,
    freeGradedLinear_homogeneous, homogeneousGradedMap_succ, homogeneousGradedMap_succ,
    homogeneousGradedMap_succ, gradedClass_lie]
  have he : (i + 1) + (j + 1) = (i + j + 1) + 1 := by omega
  generalize ha : homogeneousRelationTerm i x = a
  generalize hb : homogeneousRelationTerm j y = b
  have hval : (homogeneousRelationTerm (i + j + 1) z : Auxiliary.Free ℤ) =
      ⁅(a : Auxiliary.Free ℤ), (b : Auxiliary.Free ℤ)⁆ := by
    rw [← ha, ← hb]
    change ((relationFreeMap ⁅(x : RelationFree), (y : RelationFree)⁆ : Auxiliary.relationIdeal ℤ) :
      Auxiliary.Free ℤ) = _
    rw [LieHom.map_lie]
    rfl
  exact gradedClass_congr he.symm hval

/-- The grading comparison is a Lie homomorphism for the actual bracket. -/
theorem freeGradedLinear_lie (x y : RelationFree) :
    freeGradedLinear ⁅x, y⁆ = ⁅freeGradedLinear x, freeGradedLinear y⁆ := by
  refine FreeHomogeneous.homogeneous_induction RelationBasisIndex
    (fun x => freeGradedLinear ⁅x, y⁆ = ⁅freeGradedLinear x, freeGradedLinear y⁆) ?_ ?_ ?_ x
  · simp only [zero_lie, map_zero]
  · intro a b ha hb
    simp only [add_lie, map_add, ha, hb]
  · intro i a
    refine FreeHomogeneous.homogeneous_induction RelationBasisIndex
      (fun y => freeGradedLinear ⁅(a : RelationFree), y⁆ =
        ⁅freeGradedLinear a, freeGradedLinear y⁆) ?_ ?_ ?_ y
    · simp only [lie_zero, map_zero]
    · intro b c hb hc
      simp only [lie_add, map_add, hb, hc]
    · intro j b
      exact freeGradedLinear_lie_homogeneous i j a b

def freeGradedHom : RelationFree →ₗ⁅ℤ⁆ ReducedGraded :=
  { freeGradedLinear with map_lie' := freeGradedLinear_lie _ _ }

end Parafree.TheoremA.RationalModel
