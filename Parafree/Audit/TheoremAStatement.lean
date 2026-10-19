import Parafree.TheoremA.Complete

/- Independent type checks of the manuscript's objects and both numbered assertions. -/
noncomputable section
open Parafree.TheoremA Parafree.Lie LieRings.Homological.LieHomology
open scoped TensorProduct

-- The quotient has exactly these three ideal relators, not extra equations.
example : relationIdeal = LieSubmodule.lieSpan ℤ PresentationFree
    (Set.range (![presentationX 0 - (⁅presentationX 1, presentationX 2⁆ + 2 • presentationQ 0),
      presentationX 1 - (⁅presentationX 2, presentationX 0⁆ + 2 • presentationQ 1),
      presentationX 2 - (2 • presentationQ 2 - ⁅presentationX 0, presentationX 1⁆)])) := by
  unfold relationIdeal
  congr 2
  funext i
  fin_cases i <;> rfl
example : K = (PresentationFree ⧸ relationIdeal) := rfl

example : K.x 0 = ⁅K.x 1, K.x 2⁆ + 2 • K.q 0 := K.relation_z
example : K.x 1 = ⁅K.x 2, K.x 0⁆ + 2 • K.q 1 := K.relation_u
example : K.x 2 = 2 • K.q 2 - ⁅K.x 0, K.x 1⁆ := K.relation_v
example : L = (K ⧸ (⨅ n, LieModule.lowerCentralSeries ℤ K K n)) := rfl
example (i : Fin 3) :
    freeToL (FreeLieAlgebra.of ℤ i) = quotientMk (residualIdeal ℤ K) (K.q i) := freeToL_of i
example : IsParafree L 3 ∧ IsParaEquivalence freeToL := ⟨theoremA.1, theoremA.2.1⟩
example : Nonempty ((Homology (R := ℤ) (L := L) 2 ⊗[ℤ] ZMod 2) ≃ₗ[ℤ] ZMod 2) :=
  ⟨homologyTwoTensorRightEquiv⟩
example : Nonempty ((ZMod 2 ⊗[ℤ] Homology (R := ℤ) (L := L) 2) ≃ₗ[ZMod 2] ZMod 2) :=
  theoremA.2.2
