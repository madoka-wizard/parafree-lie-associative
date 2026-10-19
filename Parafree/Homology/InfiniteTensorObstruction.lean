import Parafree.Homology.FinitePresentation

/-! Infinite scalar-reduced homology obstructs a finite Lie presentation. -/
noncomputable section
namespace Parafree.Homology.FinitePresentation
open Parafree.Lie LieRings.Homological.LieHomology
open scoped TensorProduct
variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {K : Type*} [Field K] [Algebra R K]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-- An actual linear equivalence with a countable direct sum implies both
non-finite generation of integral homology and non-finite presentability. -/
theorem infinite_tensor_obstruction
    (e : (K ⊗[R] Homology (R := R) (L := L) 2) ≃ₗ[K] (ℕ →₀ K)) :
    ¬ Module.Finite R (Homology (R := R) (L := L) 2) ∧ ¬ IsFinitelyPresented R L := by
  have hn : ¬ Module.Finite R (Homology (R := R) (L := L) 2) := by
    intro h
    letI := h
    letI : Module.Finite K (ℕ →₀ K) := Module.Finite.of_surjective e.toLinearMap e.surjective
    haveI : Finite ℕ := (Finsupp.basisSingleOne : Module.Basis ℕ K (ℕ →₀ K)).linearIndependent.finite
    exact not_finite ℕ
  exact ⟨hn,not_finitelyPresented_of_homologyTwo_not_finite hn⟩

end Parafree.Homology.FinitePresentation
