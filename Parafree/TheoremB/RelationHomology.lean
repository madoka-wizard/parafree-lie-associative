import Parafree.TheoremB.AuxiliaryHomologyThree
import Parafree.Homology.Coefficients.FoxDimensionShift

/-! Actual coefficient homology of the relation module for the exact
auxiliary presentation. This is the target of the divided-relator transfer. -/
noncomputable section
namespace Parafree.TheoremB.Auxiliary
open Parafree.Homology.Coefficients

abbrev RelationCoefficients := FoxSequence.RelationCoefficients K (Fin 2) (relationIdeal K)

def relationCoefficientEquiv :
    LieRings.Homological.LieHomology.Abelianization K (relationIdeal K) ≃ₗ[K] RelationCoefficients :=
  FoxSequence.relationEquiv K (Fin 2) (relationIdeal K)

def relationHomologyOneEquiv : Homology K (Presented K) RelationCoefficients 1 ≃ₗ[K] (ℕ →₀ K) :=
  (FoxSequence.relationHomologyEquiv K (Fin 2) (relationIdeal K) 1 (by decide)).trans
    presentedModFive_homologyThreeEquiv

end Parafree.TheoremB.Auxiliary
