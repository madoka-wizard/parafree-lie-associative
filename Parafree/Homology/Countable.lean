import Parafree.Homology.Concrete
import Mathlib.Data.Finsupp.Encodable

/-! Countability bounds for actual exterior chains and CE homology. -/
noncomputable section
namespace Parafree.Homology

attribute [local instance] Concrete.quotientAddCommMonoid

variable (R : Type*) [CommRing R] [Countable R]

theorem exteriorPower_countable (M : Type*) [AddCommGroup M] [Module R M]
    [Countable M] (n : ℕ) : Countable (⋀[R]^n M) := by
  have hs : Function.Surjective (Finsupp.linearCombination R (exteriorPower.ιMulti R n (M := M))) :=
    LinearMap.range_eq_top.mp (by rw [Finsupp.range_linearCombination, exteriorPower.ιMulti_span])
  exact hs.countable

theorem homology_countable (L : Type*) [LieRing L] [LieAlgebra R L]
    [Countable L] (n : ℕ) :
    Countable (LieRings.Homological.LieHomology.Homology (R := R) (L := L) (n+1)) := by
  letI := exteriorPower_countable R L (n+1)
  letI : Countable (Concrete.Quotient R L n) :=
    (Submodule.mkQ_surjective (LinearMap.range (Concrete.boundary R L n))).countable
  exact (Concrete.equiv R L n).injective.countable

end Parafree.Homology
