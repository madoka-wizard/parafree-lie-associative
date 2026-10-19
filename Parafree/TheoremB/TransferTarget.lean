import Parafree.TheoremB.RelationHomology
import Parafree.TheoremB.AuxiliarySection
import Parafree.Homology.Coefficients.SplitInjection
import Parafree.Homology.InfiniteTensorObstruction

/-! Consequences of concrete split-injection data for Theorem B.
`ConcreteTransfer.data` supplies these data without extra hypotheses, and
`Complete.lean` applies the consequences to obtain the full theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB
open LieRings.Homological.LieHomology
open scoped TensorProduct

instance P_countable : Countable P := by
  letI : Countable (FreeAlgebra ℤ (Fin 2)) := (FreeAlgebra.basisFreeMonoid ℤ (Fin 2)).repr.injective.countable
  letI : Countable IntegralFree := (LieRings.FreeLieDimension.freeLieToFreeAlgebra_injective_int (Fin 2)).countable
  exact integralEquiv.symm.injective.countable

instance PmodFive_countable : Countable PmodFive := by
  letI : Countable (Parafree.Linear.ModScalar.Quotient (5:ℤ) P) :=
    (Parafree.Linear.ModScalar.mk_surjective (5:ℤ) P).countable
  exact (Parafree.Linear.ModScalar.tensorNatEquiv 5 P).injective.countable

instance reducedHomologyTwo_countable : Countable (Homology (R := ZMod 5) (L := PmodFive) 2) :=
  Parafree.Homology.homology_countable (ZMod 5) PmodFive 1

abbrev TransferData := Parafree.Homology.Coefficients.SplitInjectionData
  (ZMod 5) (Auxiliary.Presented (ZMod 5)) PmodFive Auxiliary.RelationCoefficients

def homologyTwoEquivOfTransfer (S : TransferData) :
    Homology (R := ZMod 5) (L := PmodFive) 2 ≃ₗ[ZMod 5] (ℕ →₀ ZMod 5) := by
  apply Parafree.Linear.countableInfiniteDimensionalEquiv
  intro hf
  letI := hf
  let f := S.homologyInjection.comp Auxiliary.relationHomologyOneEquiv.symm.toLinearMap
  have hfin : Module.Finite (ZMod 5) (ℕ →₀ ZMod 5) :=
    Module.Finite.of_injective f (S.homologyInjection_injective.comp Auxiliary.relationHomologyOneEquiv.symm.injective)
  letI := hfin
  haveI : Finite ℕ := (Finsupp.basisSingleOne : Module.Basis ℕ (ZMod 5) (ℕ →₀ ZMod 5)).linearIndependent.finite
  exact not_finite ℕ

def homologyTwoTensorEquivOfTransfer (S : TransferData) :
    (ZMod 5 ⊗[ℤ] Homology (R := ℤ) (L := P) 2) ≃ₗ[ZMod 5] (ℕ →₀ ZMod 5) :=
  homologyTwoTensorModFiveEquiv.trans (homologyTwoEquivOfTransfer S)

theorem not_finitelyPresented_of_transfer (S : TransferData) :
    ¬ Module.Finite ℤ (Homology (R := ℤ) (L := P) 2) ∧ ¬ Parafree.Lie.IsFinitelyPresented ℤ P :=
  Parafree.Homology.FinitePresentation.infinite_tensor_obstruction (homologyTwoTensorEquivOfTransfer S)

end Parafree.TheoremB
