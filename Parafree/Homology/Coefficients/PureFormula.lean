import Parafree.Homology.Coefficients.LowDegree

/-!
# Separating bracket and coefficient terms of the CE differential

The formula is valid over every commutative ring, in every exterior degree,
for an arbitrary left Lie module. The exterior-only differential is the actual
upstream differential. This separation makes the PBW filtration estimate a
coefficientwise argument without an explicit double sum of bracket terms.
-/

noncomputable section

namespace Parafree.Homology.Coefficients

open scoped TensorProduct
open Parafree.Linear.ExteriorTensor

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

omit [LieRing L] in
private theorem removeNth_succ_tail {n : ℕ} (v : Fin (n + 2) → L) (i : Fin (n + 1)) :
    i.succ.removeNth v = Fin.cons (v 0) (i.removeNth (Fin.tail v)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Fin.removeNth, Fin.succAbove_ne_zero_zero]
  · simp [Fin.removeNth, Fin.tail]

theorem boundary_pure_separation (n : ℕ) (v : Fin (n + 1) → L) (m : M) :
    boundary R L M (ExteriorAlgebra.ιMulti R (n + 1) v ⊗ₜ[R] m) =
      LieRings.Homological.LieHomology.boundary R L
        (ExteriorAlgebra.ιMulti R (n + 1) v) ⊗ₜ[R] m +
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
        (ExteriorAlgebra.ιMulti R n (i.removeNth v) ⊗ₜ[R] ⁅v i, m⁆) := by
  induction n with
  | zero =>
    rw [Fin.sum_univ_succ]
    simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
      mul_one, boundary_ι_tmul, LieRings.Homological.LieHomology.boundary_ι,
      TensorProduct.zero_tmul, Fin.val_zero, pow_zero, one_smul, zero_add,
      Fin.sum_univ_zero, add_zero]
  | succ n ih =>
    have hw (i : Fin (n + 1)) :
        ExteriorAlgebra.ιMulti R (n + 1) (i.succ.removeNth v) =
          ExteriorAlgebra.ι R (v 0) *
            ExteriorAlgebra.ιMulti R n (i.removeNth (Matrix.vecTail v)) := by
      rw [removeNth_succ_tail, ExteriorAlgebra.ιMulti_succ_apply]
      rfl
    rw [ExteriorAlgebra.ιMulti_succ_apply, ← prepend_tmul, boundary_prepend,
      action_tmul, ih, map_add, prepend_tmul,
      LieRings.Homological.LieHomology.boundary_ι_mul,
      TensorProduct.sub_tmul]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero,
      Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
      hw, map_sum, map_smul, prepend_tmul, Finset.sum_neg_distrib,
      Matrix.vecTail, Function.comp_apply]
    change _ = _ + ((ExteriorAlgebra.ιMulti R (n + 1) (v ∘ Fin.succ) ⊗ₜ[R] ⁅v 0, m⁆) + _)
    abel

/-- The all-degree coefficient differential is the exterior-only differential
minus the alternating sum of coefficient actions. -/
theorem differential_pure_separation (n : ℕ) (v : Fin (n + 1) → L) (m : M) :
    differential R L M n (pure R L M (n + 1) v m) =
      LieRings.Homological.LieHomology.differential R L n
        (exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] m -
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • pure R L M n (i.removeNth v) ⁅v i, m⁆ := by
  apply inclusion_injective R L M n
  simp only [inclusion_differential, inclusion_pure, map_sub, map_sum, map_smul,
    inclusion_tmul, LieRings.Homological.LieHomology.differential_coe,
    TensorProduct.neg_tmul, boundary_pure_separation, neg_add_rev]
  abel

end Parafree.Homology.Coefficients
