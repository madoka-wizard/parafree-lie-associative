import LieRings.Homological.LieHomology.Differential
import Mathlib.Algebra.Lie.TensorProduct

/-!
# The coefficient Chevalley--Eilenberg operator

For an arbitrary Lie module over a commutative ring, construct the coefficient
boundary on `ExteriorAlgebra R L ⊗[R] M`. The construction uses the universal
property of the exterior algebra; no basis or division is required.

`boundary` uses the positive-bracket recursion. Its negative, restricted to
homogeneous degrees, will agree with the upstream CE sign convention.
-/

noncomputable section

namespace Parafree.Homology.Coefficients

open scoped TensorProduct
open LieRings.Homological.LieHomology (adExterior)

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M]

abbrev Total := ExteriorAlgebra R L ⊗[R] M

private def exteriorLeft (x : L) : ExteriorAlgebra R L →ₗ[R] ExteriorAlgebra R L where
  toFun u := ExteriorAlgebra.ι R x * u
  map_add' _ _ := mul_add _ _ _
  map_smul' _ _ := mul_smul_comm _ _ _

/-- Exterior multiplication in the first factor, linear in the inserted vector. -/
def prepend : L →ₗ[R] Module.End R (Total R L M) where
  toFun x := TensorProduct.map (exteriorLeft R L x) LinearMap.id
  map_add' x y := by
    apply TensorProduct.ext'
    intro u m
    simp [exteriorLeft, add_mul, TensorProduct.add_tmul]
  map_smul' r x := by
    apply TensorProduct.ext'
    intro u m
    simp [exteriorLeft, TensorProduct.smul_tmul']

@[simp] theorem prepend_tmul (x : L) (u : ExteriorAlgebra R L) (m : M) :
    prepend R L M x (u ⊗ₜ[R] m) = (ExteriorAlgebra.ι R x * u) ⊗ₜ[R] m := rfl

variable [LieRingModule L M] [LieModule R L M]

/-- The diagonal action: exterior adjoint action plus the given module action. -/
def action : L →ₗ[R] Module.End R (Total R L M) where
  toFun x := TensorProduct.map (adExterior R L x) LinearMap.id +
    TensorProduct.map LinearMap.id (LieModule.toEnd R L M x)
  map_add' x y := by
    apply TensorProduct.ext'
    intro u m
    simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_apply,
      map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  map_smul' r x := by
    apply TensorProduct.ext'
    intro u m
    simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_apply,
      map_smul, LinearMap.smul_apply, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_add, RingHom.id_apply]

@[simp] theorem action_tmul (x : L) (u : ExteriorAlgebra R L) (m : M) :
    action R L M x (u ⊗ₜ[R] m) =
      adExterior R L x u ⊗ₜ[R] m + u ⊗ₜ[R] ⁅x, m⁆ := rfl

omit [LieRingModule L M] [LieModule R L M] in
theorem prepend_square (x : L) (t : Total R L M) :
    prepend R L M x (prepend R L M x t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | tmul u m =>
    rw [prepend_tmul, prepend_tmul, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
      zero_mul, TensorProduct.zero_tmul]

theorem action_prepend (x y : L) (t : Total R L M) :
    action R L M x (prepend R L M y t) =
      prepend R L M ⁅x, y⁆ t + prepend R L M y (action R L M x t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | add a b ha hb => simp only [map_add, ha, hb]; abel
  | tmul u m =>
    simp only [prepend_tmul, action_tmul,
      LieRings.Homological.LieHomology.adExterior_ι_mul, TensorProduct.add_tmul, map_add]
    abel

theorem action_lie (x y : L) (t : Total R L M) :
    action R L M ⁅x, y⁆ t =
      action R L M x (action R L M y t) - action R L M y (action R L M x t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero]
  | add a b ha hb => simp only [map_add, ha, hb]; abel
  | tmul u m =>
    simp only [action_tmul, map_add, LieRings.Homological.LieHomology.adExterior_lie,
      LinearMap.sub_apply, LinearMap.comp_apply, TensorProduct.sub_tmul,
      lie_lie, TensorProduct.tmul_sub]
    abel

private def step : L →ₗ[R]
    (ExteriorAlgebra R L × (M →ₗ[R] Total R L M)) →ₗ[R] (M →ₗ[R] Total R L M) where
  toFun x :=
    { toFun := fun p => (action R L M x).comp (TensorProduct.mk R _ _ p.1) -
        (prepend R L M x).comp p.2
      map_add' := by
        intro p q
        ext m
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
          Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
        abel
      map_smul' := by
        intro r p
        ext m
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
          Prod.smul_fst, Prod.smul_snd, LinearMap.smul_apply, TensorProduct.smul_tmul',
          map_smul, smul_sub, RingHom.id_apply]
        rw [← TensorProduct.smul_tmul', map_smul] }
  map_add' x y := by
    apply LinearMap.ext
    intro p
    apply LinearMap.ext
    intro m
    change action R L M (x + y) (p.1 ⊗ₜ[R] m) - prepend R L M (x + y) (p.2 m) =
      (action R L M x (p.1 ⊗ₜ[R] m) - prepend R L M x (p.2 m)) +
      (action R L M y (p.1 ⊗ₜ[R] m) - prepend R L M y (p.2 m))
    simp only [map_add, LinearMap.add_apply]
    abel
  map_smul' r x := by
    apply LinearMap.ext
    intro p
    apply LinearMap.ext
    intro m
    change action R L M (r • x) (p.1 ⊗ₜ[R] m) - prepend R L M (r • x) (p.2 m) =
      r • (action R L M x (p.1 ⊗ₜ[R] m) - prepend R L M x (p.2 m))
    simp only [map_smul, LinearMap.smul_apply, smul_sub]

private theorem step_apply (x : L) (p : ExteriorAlgebra R L × (M →ₗ[R] Total R L M))
    (m : M) : step R L M x p m =
      action R L M x (p.1 ⊗ₜ[R] m) - prepend R L M x (p.2 m) := rfl

private theorem step_square (x : L) (u : ExteriorAlgebra R L)
    (du : M →ₗ[R] Total R L M) :
    step R L M x (ExteriorAlgebra.ι R x * u, step R L M x (u, du)) = 0 := by
  ext m
  simp only [step_apply, LinearMap.zero_apply]
  rw [← prepend_tmul, action_prepend, lie_self, map_zero, LinearMap.zero_apply,
    zero_add, map_sub, prepend_square, sub_zero, sub_self]

/-- The bilinear coefficient boundary before passing to the tensor product. -/
def boundaryBilinear : ExteriorAlgebra R L →ₗ[R] M →ₗ[R] Total R L M :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R L) (step R L M)
    (by intro x u du; simpa using step_square R L M x u du) 0

@[simp] theorem boundaryBilinear_algebraMap (r : R) :
    boundaryBilinear R L M (algebraMap R (ExteriorAlgebra R L) r) = 0 := by
  unfold boundaryBilinear
  rw [CliffordAlgebra.foldr'_algebraMap, smul_zero]

theorem boundaryBilinear_prepend (x : L) (u : ExteriorAlgebra R L) (m : M) :
    boundaryBilinear R L M (ExteriorAlgebra.ι R x * u) m =
      action R L M x (u ⊗ₜ[R] m) - prepend R L M x (boundaryBilinear R L M u m) := by
  unfold boundaryBilinear
  rw [CliffordAlgebra.foldr'_ι_mul]
  rfl

/-- The coefficient CE boundary on the total exterior module. -/
def boundary : Module.End R (Total R L M) := TensorProduct.lift (boundaryBilinear R L M)

@[simp] theorem boundary_tmul (u : ExteriorAlgebra R L) (m : M) :
    boundary R L M (u ⊗ₜ[R] m) = boundaryBilinear R L M u m := rfl

@[simp] theorem boundary_algebraMap_tmul (r : R) (m : M) :
    boundary R L M (algebraMap R (ExteriorAlgebra R L) r ⊗ₜ[R] m) = 0 := by
  rw [boundary_tmul, boundaryBilinear_algebraMap, LinearMap.zero_apply]

theorem boundary_prepend (x : L) (t : Total R L M) :
    boundary R L M (prepend R L M x t) =
      action R L M x t - prepend R L M x (boundary R L M t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero]
  | add a b ha hb => simp only [map_add, ha, hb]; abel
  | tmul u m => exact boundaryBilinear_prepend R L M x u m

theorem boundary_action_tmul (x : L) (u : ExteriorAlgebra R L) (m : M) :
    boundary R L M (action R L M x (u ⊗ₜ[R] m)) =
      action R L M x (boundary R L M (u ⊗ₜ[R] m)) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [action_tmul, LieRings.Homological.LieHomology.adExterior_algebraMap,
      TensorProduct.zero_tmul, zero_add, boundary_algebraMap_tmul, map_zero]
  | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
  | ι_mul u y hu =>
    rw [← prepend_tmul, action_prepend, map_add, boundary_prepend, boundary_prepend,
      hu, boundary_prepend, map_sub, action_prepend, action_lie]
    abel

/-- The coefficient boundary commutes with the diagonal Lie action. -/
theorem boundary_action (x : L) (t : Total R L M) :
    boundary R L M (action R L M x t) = action R L M x (boundary R L M t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u m => exact boundary_action_tmul R L M x u m

theorem boundary_boundary_tmul (u : ExteriorAlgebra R L) (m : M) :
    boundary R L M (boundary R L M (u ⊗ₜ[R] m)) = 0 := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => rw [boundary_algebraMap_tmul, map_zero]
  | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv, add_zero]
  | ι_mul u x hu =>
    rw [← prepend_tmul, boundary_prepend, map_sub, boundary_action, boundary_prepend,
      hu, map_zero, sub_zero, sub_self]

/-- Square-zero follows from the Lie-module identity, with no characteristic assumptions. -/
theorem boundary_boundary (t : Total R L M) : boundary R L M (boundary R L M t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | tmul u m => exact boundary_boundary_tmul R L M u m

end Parafree.Homology.Coefficients
