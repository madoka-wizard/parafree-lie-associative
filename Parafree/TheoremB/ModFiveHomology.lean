import Parafree.TheoremB.Abelianization
import Parafree.Homology.ModNat

/-! Universal coefficients for the actual Lie ring of Theorem B. -/

noncomputable section
namespace Parafree.TheoremB

open LieRings.Homological.LieHomology
open scoped TensorProduct

abbrev PmodFive := ZMod 5 ⊗[ℤ] P

def homologyTwoTensorModFiveEquiv :
    (ZMod 5 ⊗[ℤ] Homology (R := ℤ) (L := P) 2) ≃ₗ[ZMod 5]
      Homology (R := ZMod 5) (L := PmodFive) 2 :=
  Parafree.Homology.ModNat.homologyTwoTensorEquiv P 5

/-- The tensor order used in the manuscript, viewed as an integral equivalence. -/
def homologyTwoTensorRightModFiveEquiv :
    (Homology (R := ℤ) (L := P) 2 ⊗[ℤ] ZMod 5) ≃ₗ[ℤ]
      Homology (R := ZMod 5) (L := PmodFive) 2 :=
  ((TensorProduct.comm ℤ _ _).toAddEquiv.trans
    homologyTwoTensorModFiveEquiv.toAddEquiv).toIntLinearEquiv

end Parafree.TheoremB
