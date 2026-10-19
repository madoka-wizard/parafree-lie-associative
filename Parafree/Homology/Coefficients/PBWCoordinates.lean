import Parafree.Homology.Coefficients.Enveloping
import Parafree.Homology.Koszul.Homogeneous
import Parafree.Associative.FilteredPBW

/-!
# PBW coordinates on regular-coefficient Lie chains

These are equivalences of chain groups, together with the transported CE
differential and its square-zero identity. The lower-filtration comparison is
proved in `PBWLeading`, and `RegularAcyclicity` applies finite descent to obtain
positive-degree exactness of the actual coefficient complex.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.PBWCoordinates

open Module
open scoped TensorProduct Parafree.Homology.Koszul
open Parafree.Linear.ExteriorTensor (Chain)
open Parafree.Homology.Koszul (Polynomial PolynomialChain exteriorBasis coefficientLevel)

universe u
variable {R L σ : Type u} [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder σ]
  (b : Basis σ R L)

/-- The polynomial coefficient coordinates of the left regular module. -/
def coefficients : Enveloping.Regular R L ≃ₗ[R] Polynomial R σ :=
  (Enveloping.equiv R L).trans (Parafree.Associative.FilteredPBW.equiv b).symm

/-- Scalar extension of the exterior basis followed by its polynomial version. -/
def exterior (n : ℕ) :
    (Polynomial R σ ⊗[R] (⋀[R]^n L)) ≃ₗ[Polynomial R σ] PolynomialChain R σ n :=
  ((b.exteriorPower n).baseChange (Polynomial R σ)).equiv
    (exteriorBasis R σ n) (Equiv.refl _)

theorem exterior_tmul_basis (n : ℕ) (p : Polynomial R σ) (s : Set.powersetCard σ n) :
    exterior b n (p ⊗ₜ[R] b.exteriorPower n s) = p • exteriorBasis R σ n s := by
  have h : p ⊗ₜ[R] b.exteriorPower n s =
      p • ((b.exteriorPower n).baseChange (Polynomial R σ)) s := by
    simp only [Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul]
  simp only [exterior, Basis.equiv_apply, Equiv.refl_apply]

/-- PBW and the exterior bases identify regular-coefficient CE chain groups
with the chain groups of the polynomial Koszul complex, over the base ring. -/
def chains (n : ℕ) : Chain R L (Enveloping.Regular R L) n ≃ₗ[R] PolynomialChain R σ n :=
  (TensorProduct.congr (LinearEquiv.refl R _) (coefficients b)).trans
    ((TensorProduct.comm R _ _).trans ((exterior b n).restrictScalars R))

theorem chains_tmul_basis (n : ℕ) (m : Enveloping.Regular R L)
    (s : Set.powersetCard σ n) :
    chains b n (b.exteriorPower n s ⊗ₜ[R] m) =
      coefficients b m • exteriorBasis R σ n s := by
  simp only [chains, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, TensorProduct.comm_tmul, LinearEquiv.restrictScalars_apply]
  exact exterior_tmul_basis b n _ s

/-- The actual CE differential transported into polynomial coordinates. -/
def differential (n : ℕ) : PolynomialChain R σ (n + 1) →ₗ[R] PolynomialChain R σ n :=
  (chains b n).toLinearMap.comp
    ((Coefficients.differential R L (Enveloping.Regular R L) n).comp
      (chains b (n + 1)).symm.toLinearMap)

theorem differential_chains (n : ℕ) (c : Chain R L (Enveloping.Regular R L) (n + 1)) :
    differential b n (chains b (n + 1) c) =
      chains b n (Coefficients.differential R L (Enveloping.Regular R L) n c) := by
  simp [differential]

theorem differential_comp_differential (n : ℕ) :
    (differential b n).comp (differential b (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, differential, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [show Coefficients.differential R L (Enveloping.Regular R L) n
      (Coefficients.differential R L (Enveloping.Regular R L) (n + 1)
        ((chains b (n + 2)).symm x)) = 0 from
    LinearMap.congr_fun (Coefficients.differential_comp_differential R L
      (Enveloping.Regular R L) n) _]
  simp

/-- PBW coefficient filtration on the original Lie chain group. The exterior
degree has not yet been added to the index. -/
def level (n k : ℕ) : Submodule R (Chain R L (Enveloping.Regular R L) n) :=
  (coefficientLevel R σ n k).comap (chains b n).toLinearMap

theorem level_exhaustive (n : ℕ) (c : Chain R L (Enveloping.Regular R L) n) :
    ∃ k, c ∈ level b n k :=
  Koszul.coefficientLevel_exhaustive R σ n (chains b n c)

end Parafree.Homology.Coefficients.PBWCoordinates
