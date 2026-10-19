import Parafree.Homology.Coefficients.Complex

/-! The coefficient complex with trivial scalar coefficients is the upstream CE complex.
The comparison is a chain isomorphism in all degrees, including the differential signs. -/

noncomputable section

open CategoryTheory

namespace Parafree.Homology.Coefficients

open scoped TensorProduct
open Parafree.Linear.ExteriorTensor
open LieRings.Homological.LieHomology (adExterior)

universe u v
variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Scalar coefficients with zero action, using Mathlib's type synonym. -/
abbrev Trivial := TrivialLieModule R L R

def trivialTotalEquiv : Total R L (Trivial R L) ≃ₗ[R] ExteriorAlgebra R L :=
  (TensorProduct.congr (LinearEquiv.refl R _) (TrivialLieModule.equiv R L R)).trans
    (TensorProduct.rid R _)

@[simp] theorem trivialTotalEquiv_tmul (u : ExteriorAlgebra R L) (r : Trivial R L) :
    trivialTotalEquiv R L (u ⊗ₜ[R] r) = (TrivialLieModule.equiv R L R r) • u := rfl

theorem trivialTotalEquiv_prepend (x : L) (t : Total R L (Trivial R L)) :
    trivialTotalEquiv R L (prepend R L (Trivial R L) x t) =
      ExteriorAlgebra.ι R x * trivialTotalEquiv R L t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | add a b ha hb => simp only [map_add, ha, hb, mul_add]
  | tmul u r => simp only [prepend_tmul, trivialTotalEquiv_tmul, mul_smul_comm]

theorem trivialTotalEquiv_action (x : L) (t : Total R L (Trivial R L)) :
    trivialTotalEquiv R L (action R L (Trivial R L) x t) =
      adExterior R L x (trivialTotalEquiv R L t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u r => simp [action_tmul]

theorem trivialTotalEquiv_boundary_tmul (u : ExteriorAlgebra R L) (r : Trivial R L) :
    trivialTotalEquiv R L (boundary R L (Trivial R L) (u ⊗ₜ[R] r)) =
      LieRings.Homological.LieHomology.boundary R L (trivialTotalEquiv R L (u ⊗ₜ[R] r)) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap a =>
    simp only [boundary_algebraMap_tmul, map_zero, trivialTotalEquiv_tmul, map_smul,
      LieRings.Homological.LieHomology.boundary_algebraMap, smul_zero]
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | ι_mul u x hu =>
    rw [← prepend_tmul, boundary_prepend, map_sub, trivialTotalEquiv_action,
      trivialTotalEquiv_prepend, hu, trivialTotalEquiv_prepend,
      LieRings.Homological.LieHomology.boundary_ι_mul]

theorem trivialTotalEquiv_boundary (t : Total R L (Trivial R L)) :
    trivialTotalEquiv R L (boundary R L (Trivial R L) t) =
      LieRings.Homological.LieHomology.boundary R L (trivialTotalEquiv R L t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u r => exact trivialTotalEquiv_boundary_tmul R L u r

def trivialChainEquiv (n : ℕ) : Chain R L (Trivial R L) n ≃ₗ[R] ⋀[R]^n L :=
  (TensorProduct.congr (LinearEquiv.refl R _) (TrivialLieModule.equiv R L R)).trans
    (TensorProduct.rid R _)

theorem trivialChainEquiv_coe (n : ℕ) (c : Chain R L (Trivial R L) n) :
    (trivialChainEquiv R L n c : ExteriorAlgebra R L) =
      trivialTotalEquiv R L (inclusion R L (Trivial R L) n c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero, Submodule.coe_zero]
  | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]
  | tmul u r => rfl

theorem trivialChainEquiv_differential (n : ℕ) (c : Chain R L (Trivial R L) (n + 1)) :
    trivialChainEquiv R L n (differential R L (Trivial R L) n c) =
      LieRings.Homological.LieHomology.differential R L n (trivialChainEquiv R L (n + 1) c) := by
  apply Subtype.ext
  rw [trivialChainEquiv_coe, inclusion_differential, map_neg, trivialTotalEquiv_boundary,
    LieRings.Homological.LieHomology.differential_coe, trivialChainEquiv_coe]

/-- Comparison with the existing trivial-coefficient complex; no freeness hypotheses. -/
def trivialComplexIso : complex R L (Trivial R L) ≅
    LieRings.Homological.LieHomology.complex R L :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (trivialChainEquiv R L n).toModuleIso)
    (fun i j hij => by
      have h : j + 1 = i := hij
      subst i
      rw [complex_d, LieRings.Homological.LieHomology.complex_d]
      ext c
      exact (trivialChainEquiv_differential R L j c).symm)

/-- Identifies the new homology with actual upstream CE homology, in every degree. -/
def trivialHomologyEquiv (n : ℕ) : Homology R L (Trivial R L) n ≃ₗ[R]
    LieRings.Homological.LieHomology.Homology (R := R) (L := L) n :=
  (HomologicalComplex.homologyMapIso (trivialComplexIso R L) n).toLinearEquiv

end Parafree.Homology.Coefficients
