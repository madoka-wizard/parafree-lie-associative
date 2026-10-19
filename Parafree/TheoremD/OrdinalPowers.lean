import Parafree.TheoremC.Separated
import Parafree.Associative.TransfinitePowers

/-! The ordinal-indexed ideal sequence of Theorem D, using the literal
successor and limit clauses from the manuscript. -/
noncomputable section
namespace Parafree.TheoremD
open Parafree.TheoremC
open Parafree.Associative
variable (k : Type*) [CommRing k]

def ordinalPower (α : Ordinal) : Ideal (A₀ k) :=
  (TransfinitePowers.power (initialAugmentationIdeal k).toTwoSided α).asIdeal

@[simp] theorem ordinalPower_nat (n : ℕ) : ordinalPower k n = initialAugmentationIdeal k ^ n := by
  simp [ordinalPower]

@[simp] theorem ordinalPower_zero : ordinalPower k 0 = ⊤ := by
  simpa only [Nat.cast_zero, Submodule.pow_zero, Ideal.one_eq_top] using ordinalPower_nat k 0

theorem ordinalPower_succ (α : Ordinal) : ordinalPower k (α+1) =
    ordinalPower k α * initialAugmentationIdeal k ⊔
      initialAugmentationIdeal k * ordinalPower k α := by
  simp [ordinalPower, TransfinitePowers.power_succ]

theorem ordinalPower_limit (α : Ordinal) (hα : Order.IsSuccLimit α) :
    ordinalPower k α = ⨅ β : Set.Iio α, ordinalPower k β.val := by
  rw [ordinalPower, TransfinitePowers.power_limit _ α hα]
  ext x
  simp [ordinalPower, TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_iInf]

/-- Identification of the first limit in the ordinal-indexed sequence. -/
theorem ordinalPower_omega_eq_kernel : ordinalPower k Ordinal.omega0 = kernel k := by
  rw [ordinalPower, TransfinitePowers.power_omega_asIdeal, Ideal.asIdeal_toTwoSided]
  exact firstLimit_eq_kernel k

end Parafree.TheoremD
