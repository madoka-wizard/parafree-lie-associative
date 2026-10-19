import Parafree.TheoremA.AuxiliaryPresentation
import Parafree.TheoremA.LowDegree
import Parafree.Homology.Equivalence

/-! Lemma S's homology statements for the actual three-relator quotient. -/

namespace Parafree.TheoremA.Auxiliary

open LieRings.Homological.LieHomology

variable (k : Type*) [Field k]

theorem homologyTwo_subsingleton : Subsingleton (Homology (R := k) (L := Presented k) 2) := by
  let e := Parafree.Homology.lieEquivHomology (equivCrossProduct k) 2
  letI := CrossProduct.homologyTwo_subsingleton k
  exact e.injective.subsingleton

noncomputable def homologyThreeEquiv : Homology (R := k) (L := Presented k) 3 ≃ₗ[k] k :=
  (Parafree.Homology.lieEquivHomology (equivCrossProduct k) 3).trans
    (CrossProduct.homologyThreeEquiv k)

end Parafree.TheoremA.Auxiliary
