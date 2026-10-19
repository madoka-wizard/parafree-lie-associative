import Parafree.Linear.CountablePID
import Parafree.TheoremA.IntegralModel
import Mathlib.SetTheory.Cardinal.Free

/-! Integral freeness needed for the homological part of Theorem A. -/

noncomputable section

namespace Parafree.TheoremA

/-- The underlying integral module is free, despite having infinite rank. -/
instance L_free : Module.Free ℤ L :=
  Linear.CountablePID.free_of_injective (FreeAlgebra.basisFreeMonoid ℤ (Fin 3))
    associativeRealization.toLinearMap associativeRealization_injective

/-- The same construction applies to every integral submodule of the concrete algebra. -/
theorem submodule_L_free (N : Submodule ℤ L) : Module.Free ℤ N :=
  Linear.CountablePID.free_of_injective (FreeAlgebra.basisFreeMonoid ℤ (Fin 3))
    (associativeRealization.toLinearMap.comp N.subtype)
    (associativeRealization_injective.comp Subtype.val_injective)

end Parafree.TheoremA
