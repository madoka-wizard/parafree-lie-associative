import Parafree.Homology.Coefficients.Complex

/-! Naturality in the coefficient module, on total chains, homogeneous chains, and homology. -/

noncomputable section

open CategoryTheory

namespace Parafree.Homology.Coefficients

open scoped TensorProduct
open Parafree.Linear.ExteriorTensor

universe u v w w'
variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {M : Type w} {N : Type w'}
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

def totalMap (f : M →ₗ⁅R,L⁆ N) : Total R L M →ₗ[R] Total R L N :=
  TensorProduct.map LinearMap.id f.toLinearMap

omit [LieModule R L M] [LieModule R L N] in
@[simp] theorem totalMap_tmul (f : M →ₗ⁅R,L⁆ N) (u : ExteriorAlgebra R L) (m : M) :
    totalMap f (u ⊗ₜ[R] m) = u ⊗ₜ[R] f m := rfl

omit [LieModule R L M] [LieModule R L N] in
theorem totalMap_prepend (f : M →ₗ⁅R,L⁆ N) (x : L) (t : Total R L M) :
    totalMap f (prepend R L M x t) = prepend R L N x (totalMap f t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u m => simp only [prepend_tmul, totalMap_tmul]

theorem totalMap_action (f : M →ₗ⁅R,L⁆ N) (x : L) (t : Total R L M) :
    totalMap f (action R L M x t) = action R L N x (totalMap f t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u m => simp only [action_tmul, totalMap_tmul, map_add, LieModuleHom.map_lie]

theorem totalMap_boundary_tmul (f : M →ₗ⁅R,L⁆ N) (u : ExteriorAlgebra R L) (m : M) :
    totalMap f (boundary R L M (u ⊗ₜ[R] m)) =
      boundary R L N (totalMap f (u ⊗ₜ[R] m)) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [boundary_algebraMap_tmul, map_zero, totalMap_tmul]
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | ι_mul u x hu =>
    rw [← prepend_tmul, boundary_prepend, map_sub, totalMap_action, totalMap_prepend,
      hu, totalMap_prepend, boundary_prepend]

theorem totalMap_boundary (f : M →ₗ⁅R,L⁆ N) (t : Total R L M) :
    totalMap f (boundary R L M t) = boundary R L N (totalMap f t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u m => exact totalMap_boundary_tmul f u m

def chainMap (f : M →ₗ⁅R,L⁆ N) (n : ℕ) : Chain R L M n →ₗ[R] Chain R L N n :=
  TensorProduct.map LinearMap.id f.toLinearMap

omit [LieModule R L M] [LieModule R L N] in
@[simp] theorem chainMap_tmul (f : M →ₗ⁅R,L⁆ N) (n : ℕ) (u : ⋀[R]^n L) (m : M) :
    chainMap f n (u ⊗ₜ[R] m) = u ⊗ₜ[R] f m := rfl

omit [LieModule R L M] [LieModule R L N] in
theorem inclusion_chainMap (f : M →ₗ⁅R,L⁆ N) (n : ℕ) (c : Chain R L M n) :
    inclusion R L N n (chainMap f n c) = totalMap f (inclusion R L M n c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u m => rfl

theorem chainMap_differential_apply (f : M →ₗ⁅R,L⁆ N) (n : ℕ) (c : Chain R L M (n + 1)) :
    chainMap f n (differential R L M n c) =
      differential R L N n (chainMap f (n + 1) c) := by
  apply inclusion_injective R L N n
  rw [inclusion_chainMap, inclusion_differential, map_neg, totalMap_boundary,
    inclusion_differential, inclusion_chainMap]

theorem chainMap_differential (f : M →ₗ⁅R,L⁆ N) (n : ℕ) :
    (chainMap f n).comp (differential R L M n) =
      (differential R L N n).comp (chainMap f (n + 1)) :=
  LinearMap.ext (chainMap_differential_apply f n)

section Categorical

variable {N' P : Type w}
  [AddCommGroup N'] [Module R N'] [LieRingModule L N'] [LieModule R L N']
  [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

/-- The morphism of all-degree complexes induced by a coefficient-module homomorphism. -/
def complexMap (f : M →ₗ⁅R,L⁆ N') : complex R L M ⟶ complex R L N' :=
  ChainComplex.ofHom (chains R L M)
    (fun n => ModuleCat.ofHom (differential R L M n)) (differential_sq R L M)
    (chains R L N') (fun n => ModuleCat.ofHom (differential R L N' n))
    (differential_sq R L N') (fun n => ModuleCat.ofHom (chainMap f n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact (chainMap_differential f n).symm)

@[simp] theorem complexMap_f (f : M →ₗ⁅R,L⁆ N') (n : ℕ) :
    (complexMap f).f n = ModuleCat.ofHom (chainMap f n) := rfl

@[simp] theorem complexMap_id : complexMap (LieModuleHom.id : M →ₗ⁅R,L⁆ M) =
    𝟙 (complex R L M) := by
  ext n c
  change chainMap (LieModuleHom.id : M →ₗ⁅R,L⁆ M) n c = c
  induction c using TensorProduct.induction_on with
  | zero => exact map_zero _
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u m => rfl

@[simp] theorem complexMap_comp (f : M →ₗ⁅R,L⁆ N') (g : N' →ₗ⁅R,L⁆ P) :
    complexMap (g.comp f) = complexMap f ≫ complexMap g := by
  ext n c
  change chainMap (g.comp f) n c = chainMap g n (chainMap f n c)
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u m => rfl

def homologyMap (f : M →ₗ⁅R,L⁆ N') (n : ℕ) : homology R L M n ⟶ homology R L N' n :=
  HomologicalComplex.homologyMap (complexMap f) n

@[simp] theorem homologyMap_id (n : ℕ) :
    homologyMap (LieModuleHom.id : M →ₗ⁅R,L⁆ M) n = 𝟙 _ := by
  rw [homologyMap, complexMap_id]
  exact HomologicalComplex.homologyMap_id (complex R L M) n

theorem homologyMap_comp (f : M →ₗ⁅R,L⁆ N') (g : N' →ₗ⁅R,L⁆ P) (n : ℕ) :
    homologyMap (g.comp f) n = homologyMap f n ≫ homologyMap g n := by
  rw [homologyMap, complexMap_comp]
  exact HomologicalComplex.homologyMap_comp (complexMap f) (complexMap g) n

end Categorical
end Parafree.Homology.Coefficients
