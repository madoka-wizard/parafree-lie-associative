import Parafree.TheoremA.DividedReduction
import Parafree.TheoremA.ModTwoHomology
import Parafree.Lie.Transport
import Parafree.Homology.Equivalence

/-! The reduced filtration grading on the actual algebra from Theorem A.
The homogeneous bracket formula fixes the transported Lie structure explicitly. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Linear
open Auxiliary (dividedFiltration)
open scoped TensorProduct

/-- Compare with scalar extension of the original residual quotient. -/
def gradedRealization : ReducedGraded ≃ₗ[ℤ] LmodTwo :=
  (dividedReductionEquiv.trans (ModScalar.congr (2 : ℤ) equivDivided.symm.toLinearEquiv)).trans
    (ModScalar.tensorTwoEquiv L).symm

/-- A homogeneous class represented by an integral filtration element. -/
def gradedClass (n : ℕ) (a : dividedFiltration n) : ReducedGraded :=
  DFinsupp.single n ((reducedLayerRelations n).mkQ a)

@[simp] theorem gradedPresentation_single (n : ℕ) (a : dividedFiltration n) :
    gradedPresentation (DFinsupp.single n a) = gradedClass n a := by
  ext j
  by_cases h : j = n
  · subst j; simp only [gradedPresentation_apply, gradedClass, DFinsupp.single_eq_same]
  · simp only [gradedPresentation_apply, gradedClass, DFinsupp.single_eq_of_ne h, map_zero]

theorem gradedRealization_class (n : ℕ) (a : dividedFiltration n) :
    gradedRealization (gradedClass n a) =
      (1 : ZMod 2) ⊗ₜ[ℤ] equivDivided.symm (dividedTerm n a) := by
  rw [← gradedPresentation_single]
  change (ModScalar.tensorTwoEquiv L).symm
    (ModScalar.congr (2 : ℤ) equivDivided.symm.toLinearEquiv
      (dividedReductionEquiv (gradedPresentation (DFinsupp.single n a)))) = _
  rw [dividedReductionEquiv_presentation]
  change (ModScalar.tensorTwoEquiv L).symm
    (ModScalar.mk (2 : ℤ) L (equivDivided.symm (sumTerms (DFinsupp.single n a)))) = _
  rw [sumTerms_single, ModScalar.tensorTwoEquiv_symm_mk]

instance reducedGradedLieRing : LieRing ReducedGraded :=
  Parafree.Lie.Transport.lieRing gradedRealization

instance reducedGradedLieAlgebra : LieAlgebra ℤ ReducedGraded :=
  Parafree.Lie.Transport.lieAlgebra gradedRealization

/-- The actual Lie equivalence; the bracket is described on every pure term below. -/
def gradedLieEquiv : ReducedGraded ≃ₗ⁅ℤ⁆ LmodTwo :=
  Parafree.Lie.Transport.equiv gradedRealization

@[simp] theorem gradedLieEquiv_apply (x : ReducedGraded) :
    gradedLieEquiv x = gradedRealization x := rfl

def filtrationBracket (i j : ℕ) (a : dividedFiltration i) (b : dividedFiltration j) :
    dividedFiltration (i + j) :=
  ⟨⁅(a : Auxiliary.Free ℤ), (b : Auxiliary.Free ℤ)⁆,
    dividedFiltration_lie_mem i j a.property b.property⟩

theorem dividedTerm_lie (i j : ℕ) (a : dividedFiltration i) (b : dividedFiltration j) :
    ⁅dividedTerm i a, dividedTerm j b⁆ = dividedTerm (i + j) (filtrationBracket i j a b) := by
  apply Subtype.ext
  change ⁅(1 / 2 : ℚ) ^ i • integralInclusion a,
    (1 / 2 : ℚ) ^ j • integralInclusion b⁆ =
      (1 / 2 : ℚ) ^ (i + j) • integralInclusion ⁅(a : Auxiliary.Free ℤ), (b : Auxiliary.Free ℤ)⁆
  rw [smul_lie, lie_smul, smul_smul, ← pow_add, LieHom.map_lie]

/-- The transported bracket is exactly the bracket induced by the integral
filtration, including degree zero and all mixed degrees. -/
theorem gradedClass_lie (i j : ℕ) (a : dividedFiltration i) (b : dividedFiltration j) :
    ⁅gradedClass i a, gradedClass j b⁆ =
      gradedClass (i + j) (filtrationBracket i j a b) := by
  apply gradedLieEquiv.injective
  rw [LieHom.map_lie]
  change ⁅gradedRealization (gradedClass i a), gradedRealization (gradedClass j b)⁆ =
    gradedRealization (gradedClass (i + j) (filtrationBracket i j a b))
  simp only [gradedRealization_class,
    LieAlgebra.ExtendScalars.bracket_tmul, one_mul, ← LieEquiv.map_lie, dividedTerm_lie]

/-- Every element of the actual reduced grading is killed by two. -/
theorem reducedGraded_two_nsmul (x : ReducedGraded) : (2 : ℕ) • x = 0 := by
  apply gradedRealization.injective
  rw [map_nsmul, map_zero]
  calc
    (2 : ℕ) • gradedRealization x = (2 : ZMod 2) • gradedRealization x :=
      (Nat.cast_smul_eq_nsmul (ZMod 2) (M := LmodTwo) 2 (gradedRealization x)).symm
    _ = 0 := by
      rw [show (2 : ZMod 2) = 0 by decide, zero_smul]

instance reducedGradedFieldModule : Module (ZMod 2) ReducedGraded :=
  AddCommGroup.zmodModule reducedGraded_two_nsmul

instance reducedGradedFieldLieAlgebra : LieAlgebra (ZMod 2) ReducedGraded where
  lie_smul c x y := by
    rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact lie_zsmul x y _

/-- The comparison is also an equivalence over the actual coefficient field. -/
def gradedFieldLieEquiv : ReducedGraded ≃ₗ⁅ZMod 2⁆ LmodTwo :=
  LieEquiv.ofBijective
    { gradedLieEquiv.toLieHom.toLinearMap.toAddMonoidHom.toZModLinearMap 2 with
      map_lie' := fun {x y} => gradedLieEquiv.map_lie x y }
    gradedLieEquiv.bijective

/-- Transport actual CE homology in every degree to the reduced grading. -/
def gradedHomologyEquiv (n : ℕ) :
    LieRings.Homological.LieHomology.Homology (R := ZMod 2) (L := ReducedGraded) n ≃ₗ[ZMod 2]
      LieRings.Homological.LieHomology.Homology (R := ZMod 2) (L := LmodTwo) n :=
  Parafree.Homology.lieEquivHomology gradedFieldLieEquiv n

/-- The original integral second homology reduces to that of the explicit grading.
This comparison does not compute the latter homology. -/
def homologyTwoTensorGradedEquiv :
    (ZMod 2 ⊗[ℤ] LieRings.Homological.LieHomology.Homology (R := ℤ) (L := L) 2) ≃ₗ[ZMod 2]
      LieRings.Homological.LieHomology.Homology (R := ZMod 2) (L := ReducedGraded) 2 :=
  homologyTwoTensorModTwoEquiv.trans (gradedHomologyEquiv 2).symm

end Parafree.TheoremA.RationalModel
