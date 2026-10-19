import Parafree.Linear.CountablePID
import LieRings.DimensionSubring.FreeLie
import Mathlib.SetTheory.Cardinal.Free

/-! Integral module freeness for countably generated free Lie algebras and
all their submodules, without a finite-rank assumption. -/

noncomputable section

namespace Parafree.Lie

variable (X : Type*) [Countable X]

theorem integral_freeLie_submodule_free (N : Submodule ℤ (FreeLieAlgebra ℤ X)) :
    Module.Free ℤ N :=
  Parafree.Linear.CountablePID.free_of_injective (FreeAlgebra.basisFreeMonoid ℤ X)
    ((LieRings.PBW.freeLieToFreeAlgebra ℤ X).toLinearMap.comp N.subtype)
    ((LieRings.FreeLieDimension.freeLieToFreeAlgebra_injective_int X).comp Subtype.val_injective)

theorem integral_freeLie_free : Module.Free ℤ (FreeLieAlgebra ℤ X) :=
  Parafree.Linear.CountablePID.free_of_injective (FreeAlgebra.basisFreeMonoid ℤ X)
    (LieRings.PBW.freeLieToFreeAlgebra ℤ X).toLinearMap
    (LieRings.FreeLieDimension.freeLieToFreeAlgebra_injective_int X)

end Parafree.Lie
