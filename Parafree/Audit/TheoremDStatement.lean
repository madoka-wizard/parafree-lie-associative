import Parafree.TheoremD

/-! Literal two-relator presentation and the exact least stationary ordinal. -/
noncomputable section
open Parafree.TheoremD Parafree.TheoremC Parafree.Associative
variable (k : Type*) [CommRing k] [Nontrivial k]

example (n : ℕ) : relator k n =
    (1+FreeAlgebra.ι k (0 : Fin 6)) * (1+FreeAlgebra.ι k (1 : Fin 6))^n *
      (1+FreeAlgebra.ι k (2 : Fin 6)) -
    (1+FreeAlgebra.ι k (3 : Fin 6)) * (1+FreeAlgebra.ι k (4 : Fin 6))^n *
      (1+FreeAlgebra.ι k (5 : Fin 6)) := rfl

example : A₀ k = (FreeAlgebra k (Fin 6) ⧸
    twoSidedSpan (Set.range (fun i : Fin 2 => relator k i))) := rfl
example : ordinalPower k Ordinal.omega0 = RingHom.ker (projection k) :=
  ordinalPower_omega_eq_kernel k
example (α : Ordinal) : ordinalPower k (α+1) =
    ordinalPower k α * RingHom.ker (augmentation₀ k) ⊔
      RingHom.ker (augmentation₀ k) * ordinalPower k α := ordinalPower_succ k α
example (α : Ordinal) (hα : Order.IsSuccLimit α) :
    ordinalPower k α = ⨅ β : Set.Iio α, ordinalPower k β.val := ordinalPower_limit k α hα
example (α : Ordinal) (hα : α < Ordinal.omega0 * Ordinal.omega0) : ordinalPower k α ≠ ⊥ :=
  ordinalPower_ne_bot_below_omega_sq k α hα
example : (⨅ n : ℕ, (RingHom.ker (projection k)) ^ n) = ⊥ :=
  KernelSeparation.kernel_iInf_pow_eq_bot k

example (h : ℕ) : ordinalPower k (Ordinal.omega0 * h) = RingHom.ker (projection k) ^ h :=
  ordinalPower_omega_mul k h
example : ordinalPower k (Ordinal.omega0 * Ordinal.omega0) =
      ordinalPower k (Ordinal.omega0 * Ordinal.omega0+1) ∧
    ∀ α < Ordinal.omega0 * Ordinal.omega0, ordinalPower k α ≠ ordinalPower k (α+1) :=
  augmentation_length_omega_sq k

example : ordinalPower k 0 = ⊤ := ordinalPower_zero k
example : ordinalPower k (Ordinal.omega0 * Ordinal.omega0) =
      ordinalPower k (Ordinal.omega0 * Ordinal.omega0+1) ∧
    ∀ α < Ordinal.omega0 * Ordinal.omega0, ordinalPower k α ≠ ordinalPower k (α+1) :=
  theoremD k
