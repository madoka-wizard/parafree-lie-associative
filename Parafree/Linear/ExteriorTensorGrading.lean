import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Homogeneous components of an exterior algebra tensored with a module

The inclusion of every exterior power remains injective after tensoring with an
arbitrary module: the exterior grading supplies an explicit linear retraction.
In particular, no flatness assumption on the coefficient module is necessary.
-/

noncomputable section

namespace Parafree.Linear.ExteriorTensor

open scoped TensorProduct DirectSum

variable (R V M : Type*) [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup M] [Module R M]

abbrev Chain (n : ℕ) := (⋀[R]^n V) ⊗[R] M
abbrev Total := ExteriorAlgebra R V ⊗[R] M

def inclusion (n : ℕ) : Chain R V M n →ₗ[R] Total R V M :=
  TensorProduct.map (⋀[R]^n V).subtype LinearMap.id

@[simp] theorem inclusion_tmul (n : ℕ) (u : ⋀[R]^n V) (m : M) :
    inclusion R V M n (u ⊗ₜ[R] m) = (u : ExteriorAlgebra R V) ⊗ₜ[R] m := rfl

def exteriorProjection (n : ℕ) : ExteriorAlgebra R V →ₗ[R] (⋀[R]^n V) :=
  (DirectSum.component R ℕ (fun i => ⋀[R]^i V) n).comp
    (DirectSum.decomposeAlgEquiv (fun i => ⋀[R]^i V)).toAlgHom.toLinearMap

@[simp] theorem exteriorProjection_subtype (n : ℕ) (u : ⋀[R]^n V) :
    exteriorProjection R V n u = u := by
  change (DirectSum.decompose (fun i => ⋀[R]^i V) u) n = u
  rw [DirectSum.decompose_of_mem (fun i => ⋀[R]^i V) u.property, DirectSum.of_eq_same]

def projection (n : ℕ) : Total R V M →ₗ[R] Chain R V M n :=
  TensorProduct.map (exteriorProjection R V n) LinearMap.id

@[simp] theorem projection_tmul (n : ℕ) (u : ExteriorAlgebra R V) (m : M) :
    projection R V M n (u ⊗ₜ[R] m) = exteriorProjection R V n u ⊗ₜ[R] m := rfl

@[simp] theorem projection_inclusion (n : ℕ) (c : Chain R V M n) :
    projection R V M n (inclusion R V M n c) = c := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u m => rw [inclusion_tmul, projection_tmul, exteriorProjection_subtype]

theorem inclusion_injective (n : ℕ) : Function.Injective (inclusion R V M n) :=
  Function.LeftInverse.injective (projection_inclusion R V M n)

abbrev component (n : ℕ) : Submodule R (Total R V M) := (inclusion R V M n).range

theorem tmul_mem_component {n : ℕ} {u : ExteriorAlgebra R V} (hu : u ∈ ⋀[R]^n V)
    (m : M) : u ⊗ₜ[R] m ∈ component R V M n := ⟨(⟨u, hu⟩ : ⋀[R]^n V) ⊗ₜ[R] m, rfl⟩

theorem inclusion_projection {n : ℕ} {t : Total R V M} (ht : t ∈ component R V M n) :
    inclusion R V M n (projection R V M n t) = t := by
  obtain ⟨c, rfl⟩ := ht
  rw [projection_inclusion]

end Parafree.Linear.ExteriorTensor
