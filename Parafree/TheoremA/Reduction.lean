import Parafree.TheoremA.Abelianization
import Parafree.TheoremA.IntegralModel

/-!
# Cycle-level prerequisites for reduction modulo two

These lemmas are stated for the actual integral CE differentials. The tensor/exterior
base-change comparison and the induced equivalence on homology are still separate work.
-/

namespace Parafree.TheoremA

open Parafree.Lie LieRings.Homological.LieHomology

noncomputable section

theorem degreeTwoBoundary_mem_derived (z : ⋀[ℤ]^2 L) :
    degreeTwoBoundary ℤ L z ∈ lowerCentral ℤ L 1 := by
  have h : degreeTwoBoundary ℤ L z ∈ LinearMap.range (degreeTwoBoundary ℤ L) := ⟨z, rfl⟩
  rw [range_degreeTwoBoundary] at h
  simpa only [lowerCentral, LieModule.lowerCentralSeries_succ,
    LieModule.lowerCentralSeries_zero] using h

/-- The second CE boundary has two-saturated image, because the abelianization has no torsion. -/
theorem degreeTwoBoundary_two_saturated {y : L}
    (h : ∃ z : ⋀[ℤ]^2 L, degreeTwoBoundary ℤ L z = (2 : ℤ) • y) :
    ∃ t : ⋀[ℤ]^2 L, degreeTwoBoundary ℤ L t = y := by
  obtain ⟨z, hz⟩ := h
  have hy2 : (2 : ℤ) • quotientMk (lowerCentral ℤ L 1) y = 0 := by
    rw [← map_smul, ← hz, quotientMk_eq_zero]
    exact degreeTwoBoundary_mem_derived z
  have hy0 : quotientMk (lowerCentral ℤ L 1) y = 0 :=
    (smul_eq_zero_iff_right (by decide : (2 : ℤ) ≠ 0)).mp hy2
  have hy := (quotientMk_eq_zero _ _).mp hy0
  change y ∈ LinearMap.range (degreeTwoBoundary ℤ L)
  rw [range_degreeTwoBoundary]
  simpa only [lowerCentral, LieModule.lowerCentralSeries_succ,
    LieModule.lowerCentralSeries_zero] using hy

/-- An integral two-chain whose boundary is even can be corrected by twice a chain to a cycle. -/
theorem lift_even_boundary_to_cycle (z : ⋀[ℤ]^2 L)
    (hz : ∃ y : L, degreeTwoBoundary ℤ L z = (2 : ℤ) • y) :
    ∃ (c t : ⋀[ℤ]^2 L), degreeTwoBoundary ℤ L c = 0 ∧ z = c + (2 : ℤ) • t := by
  obtain ⟨y, hy⟩ := hz
  obtain ⟨t, ht⟩ := degreeTwoBoundary_two_saturated ⟨z, hy⟩
  refine ⟨z - (2 : ℤ) • t, t, ?_, by abel⟩
  rw [map_sub, map_smul, hy, ht, sub_self]

theorem degreeTwoBoundary_differential_two (b : ⋀[ℤ]^3 L) :
    degreeTwoBoundary ℤ L (differential ℤ L 2 b) = 0 := by
  have h := LinearMap.congr_fun (differential_comp_differential ℤ L 1) b
  change differential ℤ L 1 (differential ℤ L 2 b) = 0 at h
  change exteriorPower.oneEquiv ℤ L (differential ℤ L 1 (differential ℤ L 2 b)) = 0
  rw [h, map_zero]

/-- If a cycle differs from a boundary by twice a chain, that chain is itself a cycle. -/
theorem even_boundary_difference_is_cycle (z a : ⋀[ℤ]^2 L) (b : ⋀[ℤ]^3 L)
    (hz : degreeTwoBoundary ℤ L z = 0)
    (h : z = differential ℤ L 2 b + (2 : ℤ) • a) :
    degreeTwoBoundary ℤ L a = 0 := by
  have ha : (2 : ℤ) • degreeTwoBoundary ℤ L a = 0 := by
    rw [h, map_add, degreeTwoBoundary_differential_two, zero_add, map_smul] at hz
    exact hz
  exact (smul_eq_zero_iff_right (by decide : (2 : ℤ) ≠ 0)).mp ha

end
end Parafree.TheoremA
