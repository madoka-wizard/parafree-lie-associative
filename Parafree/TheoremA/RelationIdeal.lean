import Parafree.TheoremA.AuxiliaryPresentation
import Parafree.Lie.IntegralFreeModule
import Parafree.Homology.Coefficients.FoxCoordinates
import Mathlib.Data.Finsupp.Encodable

/-! The integral relation ideal used in the divided-relator construction.
The higher-homology vanishing here is for this actual ideal, not for an
abstract replacement or a presumed free Lie algebra. -/

noncomputable section

namespace Parafree.TheoremA.Auxiliary

instance presented_free (R : Type*) [CommRing R] : Module.Free R (Presented R) := by
  letI : Module.Free R (CrossProduct R) := inferInstanceAs (Module.Free R (Fin 3 → R))
  exact Module.Free.of_equiv (equivCrossProduct R).symm.toLinearEquiv

instance relationIdeal_free : Module.Free ℤ (relationIdeal ℤ) :=
  Parafree.Lie.integral_freeLie_submodule_free (Fin 3) (relationIdeal ℤ).toSubmodule

/-- All higher integral CE homology of the actual relation ideal vanishes. -/
theorem relationIdeal_homology_subsingleton (n : ℕ) :
    Subsingleton (LieRings.Homological.LieHomology.Homology
      (R := ℤ) (L := relationIdeal ℤ) (n + 2)) :=
  @Parafree.Homology.Coefficients.FreeAssociative.ideal_homology_subsingleton
    ℤ (Fin 3) _ (relationIdeal ℤ) relationIdeal_free (presented_free ℤ) n

/-- The three coordinate vectors, transported to the actual auxiliary presentation. -/
def presentedBasis (R : Type*) [CommRing R] : Module.Basis (Fin 3) R (Presented R) :=
  (show Module.Basis (Fin 3) R (CrossProduct R) from Pi.basisFun R (Fin 3)).map
    (equivCrossProduct R).symm.toLinearEquiv

def envelopingBasis (R : Type*) [CommRing R] :
    Module.Basis (Fin 3 →₀ ℕ) R (LieRings.UEA R (Presented R)) :=
  Parafree.Associative.RelativePBW.basis (presentedBasis R)

/-- The integral relation module embeds in a countably based free module. -/
instance relationAbelianization_free : Module.Free ℤ
    (LieRings.Homological.LieHomology.Abelianization ℤ (relationIdeal ℤ)) :=
  Parafree.Linear.CountablePID.free_of_injective
    (Finsupp.basis (fun _ : Fin 3 => envelopingBasis ℤ))
    (Parafree.Homology.Coefficients.FoxSequence.fox ℤ (Fin 3) (relationIdeal ℤ))
    (@Parafree.Homology.Coefficients.FoxSequence.fox_injective
      ℤ (Fin 3) _ (relationIdeal ℤ) relationIdeal_free (presented_free ℤ))

end Parafree.TheoremA.Auxiliary
