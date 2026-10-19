import Parafree.Homology.Coefficients.LowDegree

/-!
# Zeroth coefficient homology and coinvariants

This identifies actual coefficient CE homology with the quotient by the span of
the action. It is the low-degree interface for extracting a relation-module
sequence from the long exact coefficient sequence, without introducing a
separate derived-functor or projective-resolution comparison.
-/

noncomputable section

namespace Parafree.Homology.Coefficients

open CategoryTheory
open scoped TensorProduct
open Parafree.Linear.ExteriorTensor

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

def actionSpan : Submodule R M := Submodule.span R {m | ∃ x : L, ∃ v : M, ⁅x, v⁆ = m}

abbrev Coinvariants := M ⧸ actionSpan R L M

omit [LieRingModule L M] [LieModule R L M] in
def zeroChainEquiv : Chain R L M 0 ≃ₗ[R] M :=
  (TensorProduct.congr (exteriorPower.zeroEquiv R L) (LinearEquiv.refl R M)).trans
    (TensorProduct.lid R M)

omit [LieRingModule L M] [LieModule R L M] in
@[simp] theorem zeroChainEquiv_pure (m : M) :
    zeroChainEquiv R L M (pure R L M 0 ![] m) = m := by
  simp [zeroChainEquiv, pure]

@[simp] theorem zeroChainEquiv_differential_pure (x : L) (m : M) :
    zeroChainEquiv R L M (differential R L M 0 (pure R L M 1 ![x] m)) = -⁅x, m⁆ := by
  rw [differential_pure_one, map_neg, zeroChainEquiv_pure]

theorem differential_zero_range_map :
    (differential R L M 0).range.map (zeroChainEquiv R L M).toLinearMap = actionSpan R L M := by
  rw [← LinearMap.range_comp]
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    change zeroChainEquiv R L M (differential R L M 0 c) ∈ actionSpan R L M
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using (actionSpan R L M).add_mem ha hb
    | tmul u m =>
      have hu : u = exteriorPower.ιMulti R 1 ![(exteriorPower.oneEquiv R L) u] := by
        apply (exteriorPower.oneEquiv R L).injective
        simp only [exteriorPower.oneEquiv_ιMulti]
        rfl
      rw [hu]
      change zeroChainEquiv R L M (differential R L M 0
        (pure R L M 1 ![(exteriorPower.oneEquiv R L) u] m)) ∈ _
      rw [zeroChainEquiv_differential_pure]
      exact (actionSpan R L M).neg_mem (Submodule.subset_span ⟨_, m, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, m, rfl⟩
    refine ⟨-pure R L M 1 ![x] m, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_neg,
      zeroChainEquiv_differential_pure, neg_neg]

/-- The categorical zeroth coefficient homology is the concrete cokernel of
the first differential. -/
def homologyZeroEquivCokernel :
    Homology R L M 0 ≃ₗ[R] Chain R L M 0 ⧸ (differential R L M 0).range :=
  (((complex R L M).isoHomologyι₀.trans
    ((complex R L M).opcyclesIsoSc' 1 0 0 (by simp) (by simp))).trans
      ((complex R L M).sc' 1 0 0).moduleCatOpcyclesIso).toLinearEquiv

/-- Actual CE zeroth homology equals the module of coinvariants. No freeness,
flatness, finite dimension, or characteristic restriction is needed. -/
def homologyZeroEquivCoinvariants : Homology R L M 0 ≃ₗ[R] Coinvariants R L M :=
  (homologyZeroEquivCokernel R L M).trans
    (Submodule.Quotient.equiv _ _ (zeroChainEquiv R L M) (differential_zero_range_map R L M))

end Parafree.Homology.Coefficients
