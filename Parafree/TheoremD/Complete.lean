import Parafree.TheoremD.OrdinalLength

/-! Theorem D of the current manuscript, over every nonzero commutative ring. -/
noncomputable section
namespace Parafree.TheoremD
open Parafree.TheoremC
universe u
variable (k : Type u) [CommRing k] [Nontrivial k]

/-- The first stationary ordinal of the actual transfinite augmentation series
of the literal two-relator algebra is omega squared. -/
theorem theoremD :
    ordinalPower k (Ordinal.omega0 * Ordinal.omega0) =
        ordinalPower k (Ordinal.omega0 * Ordinal.omega0 + 1) ∧
      ∀ α < Ordinal.omega0 * Ordinal.omega0, ordinalPower k α ≠ ordinalPower k (α+1) :=
  augmentation_length_omega_sq k

end Parafree.TheoremD
