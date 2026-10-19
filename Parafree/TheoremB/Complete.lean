import Parafree.TheoremB.ConcreteTransfer

/-! The complete Theorem B for the exact rational Lie subring in the manuscript.
The maps and homology computations used here have no additional hypotheses. -/
noncomputable section
namespace Parafree.TheoremB
open LieRings.Homological.LieHomology
open scoped TensorProduct

/-- Actual second CE homology of the reduction of the manuscript's ring. -/
def actualModFiveHomologyEquiv :
    Homology (R := ZMod 5) (L := PmodFive) 2 ≃ₗ[ZMod 5] (ℕ →₀ ZMod 5) :=
  homologyTwoEquivOfTransfer ConcreteTransfer.data

/-- Tensor reduction, with the field factor first to expose field linearity. -/
def homologyTwoTensorEquiv :
    (ZMod 5 ⊗[ℤ] Homology (R := ℤ) (L := P) 2) ≃ₗ[ZMod 5] (ℕ →₀ ZMod 5) :=
  homologyTwoTensorEquivOfTransfer ConcreteTransfer.data

/-- The order of tensor factors printed in Theorem B. -/
def homologyTwoTensorRightEquiv :
    (Homology (R := ℤ) (L := P) 2 ⊗[ℤ] ZMod 5) ≃ₗ[ℤ] (ℕ →₀ ZMod 5) :=
  ((TensorProduct.comm ℤ _ _).toAddEquiv.trans homologyTwoTensorEquiv.toAddEquiv).toIntLinearEquiv

theorem homologyTwo_not_finite : ¬ Module.Finite ℤ (Homology (R := ℤ) (L := P) 2) :=
  (not_finitelyPresented_of_transfer ConcreteTransfer.data).1

theorem not_finitelyPresented : ¬ Parafree.Lie.IsFinitelyPresented ℤ P :=
  (not_finitelyPresented_of_transfer ConcreteTransfer.data).2

/-- All conclusions of Theorem B, including its specified para-equivalence and
four-generator surjection. Finite presentation has its usual finite-relator meaning. -/
theorem theoremB :
    Parafree.Lie.IsParafree P 2 ∧ Parafree.Lie.IsParaEquivalence freeToP ∧
    Nonempty ((ZMod 5 ⊗[ℤ] Homology (R := ℤ) (L := P) 2) ≃ₗ[ZMod 5] (ℕ →₀ ZMod 5)) ∧
    Function.Surjective generatingMap ∧ ¬ Parafree.Lie.IsFinitelyPresented ℤ P :=
  ⟨theoremB_part_one.1,theoremB_part_one.2,
    ⟨homologyTwoTensorEquiv⟩,generatingMap_surjective,not_finitelyPresented⟩

end Parafree.TheoremB
