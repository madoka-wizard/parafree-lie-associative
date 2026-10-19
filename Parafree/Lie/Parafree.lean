import Parafree.Lie.LowerCentral
import Mathlib.Algebra.Lie.Free

namespace Parafree.Lie

/-- Parafreeness with the rank specified by the free generator type `Fin rank`. -/
def IsParafree (L : Type*) [LieRing L] (rank : ℕ) : Prop :=
  ResiduallyNilpotent ℤ L ∧
    ∃ f : FreeLieAlgebra ℤ (Fin rank) →ₗ⁅ℤ⁆ L, IsParaEquivalence f

end Parafree.Lie
