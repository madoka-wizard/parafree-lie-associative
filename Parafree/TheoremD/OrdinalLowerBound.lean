import Parafree.TheoremD.OrdinalPowers
import Parafree.TheoremD.KernelWitness

/-! Nonvanishing at every stage below omega squared. -/
noncomputable section
namespace Parafree.TheoremD
open Parafree.TheoremC
open Parafree.Associative
variable (k : Type*) [CommRing k]

theorem ordinalPower_antitone : Antitone (ordinalPower k) :=
  fun _ _ h => TwoSidedIdeal.asIdeal.monotone
    (TransfinitePowers.antitone (initialAugmentationIdeal k).toTwoSided h)

theorem ordinalPower_add_omega (α : Ordinal) :
    ordinalPower k (α+Ordinal.omega0) = ⨅ n : ℕ, ordinalPower k (α+n) := by
  rw [ordinalPower, TransfinitePowers.power_add_omega]
  ext x
  simp [ordinalPower, TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_iInf]

theorem ordinalPower_right_mul_pow_le (α : Ordinal) (n : ℕ) :
    ordinalPower k α * initialAugmentationIdeal k ^ n ≤ ordinalPower k (α+n) := by
  simpa only [ordinalPower, Ideal.asIdeal_toTwoSided] using
    TransfinitePowers.right_mul_pow_le (initialAugmentationIdeal k).toTwoSided α n

/-- The easy containment at all omega-multiple stages. -/
theorem kernel_pow_le_ordinalPower_omega_mul (h : ℕ) :
    kernel k ^ h ≤ ordinalPower k (Ordinal.omega0 * h) := by
  induction h with
  | zero => simp only [Nat.cast_zero, mul_zero, ordinalPower_zero]; exact le_top
  | succ h ih =>
    rw [Nat.cast_succ, mul_add, mul_one, ordinalPower_add_omega]
    apply le_iInf
    intro n
    rw [Submodule.pow_succ]
    exact (Ideal.mul_mono ih (kernel_le_finitePower k n)).trans
      (ordinalPower_right_mul_pow_le k (Ordinal.omega0 * h) n)

/-- Every stage strictly below omega squared is nonzero. -/
theorem ordinalPower_ne_bot_below_omega_sq [Nontrivial k] (α : Ordinal)
    (hα : α < Ordinal.omega0 * Ordinal.omega0) : ordinalPower k α ≠ ⊥ := by
  obtain ⟨β,hβ,hαβ⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mp hα
  obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp hβ
  intro he
  apply KernelWitness.kernel_pow_ne_bot k n
  apply le_antisymm _ bot_le
  rw [← he]
  exact (kernel_pow_le_ordinalPower_omega_mul k n).trans (ordinalPower_antitone k hαβ.le)

end Parafree.TheoremD
