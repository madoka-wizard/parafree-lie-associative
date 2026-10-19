import Parafree.TheoremA.RelationIdeal
import Parafree.TheoremA.AuxiliaryHomology
import Parafree.Homology.Coefficients.FoxDimensionShift

/-! The actual coefficient homology calculation for the auxiliary presentation.
`Complete.lean` transports this calculation to `LmodTwo` using the
divided-reduction and split-extension comparisons. -/

noncomputable section

namespace Parafree.TheoremA.Auxiliary

open Parafree.Homology.Coefficients

variable (k : Type) [Field k]

/-- The relation coefficients of the exact auxiliary presentation over the field. -/
abbrev RelationCoefficients := FoxSequence.RelationCoefficients k (Fin 3) (relationIdeal k)

/-- The coefficient module agrees with the actual relation ideal's abelianization.
Its adjoint-action compatibility is `FoxSequence.relationEquiv_adjoint`. -/
def relationCoefficientEquiv :
    LieRings.Homological.LieHomology.Abelianization k (relationIdeal k) ≃ₗ[k]
      RelationCoefficients k :=
  FoxSequence.relationEquiv k (Fin 3) (relationIdeal k)

/-- Actual first coefficient CE homology of the auxiliary algebra is one-dimensional. -/
def relationHomologyOneEquiv :
    Homology k (Presented k) (RelationCoefficients k) 1 ≃ₗ[k] k :=
  (FoxSequence.relationHomologyEquiv k (Fin 3) (relationIdeal k) 1 (by decide)).trans
    (homologyThreeEquiv k)

end Parafree.TheoremA.Auxiliary
