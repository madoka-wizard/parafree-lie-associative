import Parafree.TheoremB.Complete
noncomputable section

open Parafree.TheoremB
open LieRings.Homological.LieHomology
open scoped TensorProduct

-- Literal rational subring and original nested relators from the manuscript.
example : P = (let t := FreeLieAlgebra.of ℚ (0 : Fin 2)
    let a := FreeLieAlgebra.of ℚ (1 : Fin 2)
    let w := ⁅t,a⁆ - (2:ℤ) • a
    ↥(LieSubalgebra.lieSpan ℤ (FreeLieAlgebra ℚ (Fin 2))
      (Set.range (![t,a,(1/5:ℚ) • (⁅t,⁅t,w⁆⁆-w),
        (1/5:ℚ) • (⁅a,⁅t,⁅t,a⁆⁆⁆-⁅w,⁅w,⁅t,w⁆⁆⁆)] : Fin 4 → _)))) := rfl

example : freeToP (FreeLieAlgebra.of ℤ (0 : Fin 2)) = t :=
  FreeLieAlgebra.lift_of_apply _ _
example : freeToP (FreeLieAlgebra.of ℤ (1 : Fin 2)) = a - (2:ℤ) • u :=
  FreeLieAlgebra.lift_of_apply _ _

example : Parafree.Lie.IsParafree P 2 := theoremB.1
example : Parafree.Lie.IsParaEquivalence freeToP := theoremB.2.1
example : (Homology (R := ℤ) (L := P) 2 ⊗[ℤ] ZMod 5) ≃ₗ[ℤ] (ℕ →₀ ZMod 5) :=
  homologyTwoTensorRightEquiv
example : ∃ f : FreeLieAlgebra ℤ (Fin 4) →ₗ⁅ℤ⁆ P, Function.Surjective f :=
  ⟨generatingMap,generatingMap_surjective⟩
example : ¬ Parafree.Lie.IsFinitelyPresented ℤ P := not_finitelyPresented
example : Nonempty ((ZMod 5 ⊗[ℤ] Homology (R := ℤ) (L := P) 2) ≃ₗ[ZMod 5] (ℕ →₀ ZMod 5)) ∧
    Function.Surjective generatingMap ∧ ¬ Parafree.Lie.IsFinitelyPresented ℤ P :=
  theoremB.2.2
