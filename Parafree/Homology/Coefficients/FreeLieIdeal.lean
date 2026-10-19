import Parafree.Homology.Coefficients.FreeLieRestriction
import Parafree.Homology.Coefficients.RelativeEnveloping
import Parafree.Homology.Coefficients.RestrictionEquivalences

/-!
# Higher homology of an ideal in a free Lie algebra

The ideal and its quotient are assumed free only as modules over the base
ring. Relative PBW and the last-letter resolution prove the higher homology
vanishing; freeness of the ideal as a Lie algebra is neither assumed nor used.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.FreeAssociative

open LieRings

universe u
variable (R X : Type u) [CommRing R]
  (J : LieIdeal R (FreeLieAlgebra R X))
  [Module.Free R J] [Module.Free R (FreeLieAlgebra R X ⧸ J)]

def restrictedEnvelopingEquiv : RelativeEnveloping.Restricted J.incl ≃ₗ⁅R,J⁆
    Regular (idealAction R X J) :=
  AssociativeRestriction.regularCongr (RelativeEnveloping.action J.incl)
    (idealAction R X J) (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra R X)
    (fun x => by simp [RelativeEnveloping.action, idealAction, PBW.freeLieToFreeAlgebra])

theorem ideal_regular_exactAt (n : ℕ) (hn : n ≠ 0) :
    (complex R J (Regular (idealAction R X J))).ExactAt n :=
  exactAt_of_equiv (restrictedEnvelopingEquiv R X J).symm n hn
    (RelativeEnveloping.ideal_exactAt J n hn)

theorem ideal_regular_homology_isZero (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (homology R J (Regular (idealAction R X J)) n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (ideal_regular_exactAt R X J n hn)

theorem ideal_generators_exactAt (n : ℕ) (hn : n ≠ 0) :
    (complex R J (Generators (idealAction R X J))).ExactAt n := by
  classical
  apply exactAt_of_equiv (AssociativeRestriction.finsuppEquiv (idealAction R X J)
    X (FreeAlgebra R X)) n hn
  exact DirectSums.exactAt R J (fun _ : X => Regular (idealAction R X J)) n hn
    (fun _ => ideal_regular_exactAt R X J n hn)

theorem ideal_generators_homology_isZero (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (homology R J (Generators (idealAction R X J)) n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (ideal_generators_exactAt R X J n hn)

/-- Actual trivial-coefficient CE homology vanishes in every degree at least two. -/
theorem ideal_homology_subsingleton (n : ℕ) :
    Subsingleton (LieRings.Homological.LieHomology.Homology (R := R) (L := J) (n + 2)) := by
  let e := dimensionShift (ideal_sequence_shortExact R X J) (n + 1)
    (ideal_regular_homology_isZero R X J (n + 2) (by omega))
    (ideal_regular_homology_isZero R X J (n + 1) (by omega))
  letI := ModuleCat.subsingleton_of_isZero
    (ideal_generators_homology_isZero R X J (n + 1) (by omega))
  exact Function.Injective.subsingleton
    (((trivialHomologyEquiv R J (n + 2)).symm.trans e).injective)

end Parafree.Homology.Coefficients.FreeAssociative
