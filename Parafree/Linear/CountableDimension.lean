import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! A countable infinite-dimensional vector space is a countable direct sum.
This avoids a spanning calculation when only the abstract isomorphism type
is required and an infinite independent family is already known. -/
noncomputable section
namespace Parafree.Linear
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [Countable V]

def countableInfiniteDimensionalEquiv (h : ¬ Module.Finite K V) : V ≃ₗ[K] (ℕ →₀ K) := by
  let b := Module.Basis.ofVectorSpace K V
  letI : Infinite (Module.Basis.ofVectorSpaceIndex K V) := not_finite_iff_infinite.mp (by
    intro hf
    letI := hf
    exact h (Module.Finite.of_basis b))
  let e : Module.Basis.ofVectorSpaceIndex K V ≃ ℕ := Classical.choice inferInstance
  exact (b.reindex e).repr

end Parafree.Linear
