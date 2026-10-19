import Mathlib.LinearAlgebra.DFinsupp

/-! Finite-support lifting of scalar divisibility, without finite-dimensionality
or freeness hypotheses. -/

namespace Parafree.Linear

variable {R I : Type*} [CommRing R] {M : I → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem dfinsupp_exists_smul_iff (r : R) (a : Π₀ i, M i) :
    (∃ b, r • b = a) ↔ ∀ i, ∃ b : M i, r • b = a i := by
  constructor
  · rintro ⟨b, rfl⟩ i
    exact ⟨b i, rfl⟩
  · intro h
    have hm : a ∈ LinearMap.range
        (DFinsupp.mapRange.linearMap (fun i => (r • LinearMap.id : M i →ₗ[R] M i))) := by
      rw [DFinsupp.range_mapRangeLinearMap]
      exact fun i _ => h i
    obtain ⟨b, hb⟩ := hm
    refine ⟨b, ?_⟩
    ext i
    exact congrArg (fun x => x i) hb

end Parafree.Linear
