import Parafree.Homology.Coefficients.Complex

/-! Pure-chain formulas in degrees one and two, with the negative-action convention. -/

noncomputable section

namespace Parafree.Homology.Coefficients

open scoped TensorProduct
open Parafree.Linear.ExteriorTensor
open LieRings.Homological.LieHomology (adExterior adExterior_ι)

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem boundary_one_tmul (m : M) : boundary R L M (1 ⊗ₜ[R] m) = 0 := by
  simpa only [map_one] using boundary_algebraMap_tmul R L M 1 m

theorem boundary_ι_tmul (x : L) (m : M) :
    boundary R L M (ExteriorAlgebra.ι R x ⊗ₜ[R] m) = 1 ⊗ₜ[R] ⁅x, m⁆ := by
  have h := boundary_prepend R L M x (1 ⊗ₜ[R] m)
  have hone : adExterior R L x (1 : ExteriorAlgebra R L) = 0 := by
    simpa only [map_one] using
      LieRings.Homological.LieHomology.adExterior_algebraMap R L x 1
  simpa only [prepend_tmul, mul_one, boundary_one_tmul, map_zero, sub_zero,
    action_tmul, hone, TensorProduct.zero_tmul, zero_add] using h

theorem boundary_ι_mul_ι_tmul (x y : L) (m : M) :
    boundary R L M ((ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y) ⊗ₜ[R] m) =
      ExteriorAlgebra.ι R ⁅x, y⁆ ⊗ₜ[R] m + ExteriorAlgebra.ι R y ⊗ₜ[R] ⁅x, m⁆ -
        ExteriorAlgebra.ι R x ⊗ₜ[R] ⁅y, m⁆ := by
  rw [← prepend_tmul, boundary_prepend, boundary_ι_tmul, action_tmul, adExterior_ι,
    prepend_tmul, mul_one]

/-- A decomposable coefficient chain; the module factor is written last. -/
def pure (n : ℕ) (v : Fin n → L) (m : M) : Chain R L M n :=
  exteriorPower.ιMulti R n v ⊗ₜ[R] m

omit [LieRingModule L M] [LieModule R L M] in
@[simp] theorem inclusion_pure (n : ℕ) (v : Fin n → L) (m : M) :
    inclusion R L M n (pure R L M n v m) = ExteriorAlgebra.ιMulti R n v ⊗ₜ[R] m := rfl

theorem differential_pure_one (x : L) (m : M) :
    differential R L M 0 (pure R L M 1 ![x] m) = -pure R L M 0 ![] ⁅x, m⁆ := by
  apply inclusion_injective R L M 0
  rw [inclusion_differential, map_neg, inclusion_pure, inclusion_pure]
  simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
    Matrix.cons_val_zero, mul_one, boundary_ι_tmul]

theorem differential_pure_two (x y : L) (m : M) :
    differential R L M 1 (pure R L M 2 ![x, y] m) =
      -pure R L M 1 ![⁅x, y⁆] m - pure R L M 1 ![y] ⁅x, m⁆ +
        pure R L M 1 ![x] ⁅y, m⁆ := by
  apply inclusion_injective R L M 1
  simp only [inclusion_differential, map_add, map_sub, map_neg, inclusion_pure,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
    Matrix.cons_val_zero, mul_one]
  rw [boundary_ι_mul_ι_tmul]
  abel

end Parafree.Homology.Coefficients
