import Parafree.TheoremA.DividedModel

/-! Finite presentations of elements of the actual divided model.
A divisibility witness in the model is lifted to a finite family, so the
coefficientwise cancellation criterion applies to the actual quotient. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Auxiliary (dividedFiltration dividedValue)
open scoped BigOperators

abbrev DividedFamilies := Finsupp.submodule dividedFiltration

def dividedValueLinear : (ℕ →₀ Auxiliary.Free ℤ) →ₗ[ℤ] Ambient :=
  Finsupp.lsum ℤ (fun n => (1 / 2 : ℚ) ^ n • integralInclusion.toLinearMap)

@[simp] theorem dividedValueLinear_apply (x : ℕ →₀ Auxiliary.Free ℤ) :
    dividedValueLinear x = dividedValue x := rfl

@[simp] theorem dividedValue_single (n : ℕ) (a : Auxiliary.Free ℤ) :
    dividedValue (Finsupp.single n a) = (1 / 2 : ℚ) ^ n • integralInclusion a := by
  change (Finsupp.single n a).sum (fun j b => (1 / 2 : ℚ) ^ j • integralInclusion b) = _
  exact Finsupp.sum_single_index (by simp only [map_zero, smul_zero])

def dividedEvaluation : DividedFamilies →ₗ[ℤ] Ambient :=
  dividedValueLinear.comp DividedFamilies.subtype

theorem dividedEvaluation_mem (x : DividedFamilies) : dividedEvaluation x ∈ dividedSpan := by
  change ∑ j ∈ (x : ℕ →₀ Auxiliary.Free ℤ).support,
    (1 / 2 : ℚ) ^ j • integralInclusion ((x : ℕ →₀ Auxiliary.Free ℤ) j) ∈ dividedSpan
  apply Submodule.sum_mem
  intro j _
  exact term_mem_span j _ (x.property j)

/-- Every element of the divided model has an actual finite-support representative. -/
theorem dividedEvaluation_range : LinearMap.range dividedEvaluation = dividedSpan := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact dividedEvaluation_mem x
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, a, ha, rfl⟩
    have hsingle : Finsupp.single n a ∈ DividedFamilies := by
      intro j
      by_cases h : j = n
      · subst j; simpa only [Finsupp.single_eq_same] using ha
      · simpa only [Finsupp.single_eq_of_ne h] using (dividedFiltration j).zero_mem
    exact ⟨⟨Finsupp.single n a, hsingle⟩, dividedValue_single n a⟩

def dividedPresentation : DividedFamilies →ₗ[ℤ] dividedAlgebra :=
  dividedEvaluation.codRestrict dividedAlgebra.toSubmodule dividedEvaluation_mem

theorem dividedPresentation_surjective : Function.Surjective dividedPresentation := by
  intro x
  have hx : (x : Ambient) ∈ LinearMap.range dividedEvaluation := by
    rw [dividedEvaluation_range]
    exact x.property
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, Subtype.ext ha⟩

/-- Evenness inside the actual divided algebra forces vanishing of every
coefficient in the appropriate graded quotient. The witness is not assumed
in advance to have any prescribed denominator bound. -/
theorem dividedPresentation_even_coefficients (x : DividedFamilies)
    (h : ∃ y : dividedAlgebra, dividedPresentation x = (2 : ℤ) • y) (j : ℕ) :
    ∃ a ∈ dividedFiltration (j + 1), ∃ b ∈ dividedFiltration j,
      (x : ℕ →₀ Auxiliary.Free ℤ) j = a + (2 : ℤ) • b := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨z, rfl⟩ := dividedPresentation_surjective y
  apply Auxiliary.dividedValue_even_coefficients (x : ℕ →₀ Auxiliary.Free ℤ)
    (z : ℕ →₀ Auxiliary.Free ℤ) x.property z.property
  exact congrArg Subtype.val hy

end Parafree.TheoremA.RationalModel
