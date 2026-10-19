import Parafree.Homology.Coefficients.PBWLeading
import Parafree.Homology.FilteredExactness

/-!
# Acyclicity of regular enveloping coefficients

For a Lie algebra free as a module, the actual coefficient CE complex with
left regular enveloping coefficients is exact in every positive degree.
The proof subtracts a lifted homogeneous Koszul boundary and descends through
the finite PBW coefficient filtration. It works in arbitrary characteristic.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.PBWCoordinates

open Module CategoryTheory
open scoped Parafree.Homology.Koszul
open Parafree.Linear.ExteriorTensor (Chain)
open Parafree.Homology.Koszul (PolynomialChain coefficientLevel component)

universe u
variable {R L σ : Type u} [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder σ]
  (b : Basis σ R L)

theorem top_component_cycle (n k : ℕ) (x : PolynomialChain R σ (n + 1))
    (hx : x ∈ coefficientLevel R σ (n + 1) k) (hcycle : differential b n x = 0) :
    koszulComplex.d (Koszul.variableMap R σ) n (component R σ (n + 1) k x) = 0 := by
  have h := Koszul.component_eq_zero_of_mem R σ n k (k + 1) _
    (leading_error b n k x hx) (Nat.lt_succ_self k)
  simpa only [map_add, hcycle, map_zero, zero_add, Koszul.component_differential] using h

theorem constant_cycle_eq_zero (n : ℕ) (x : PolynomialChain R σ (n + 1))
    (hx : x ∈ coefficientLevel R σ (n + 1) 0) (hcycle : differential b n x = 0) : x = 0 := by
  have hc := top_component_cycle b n 0 x hx hcycle
  have he := Koszul.sum_component_of_mem R σ (n + 1) 0 x hx
  simp only [zero_add, Finset.sum_range_one] at he
  rw [he] at hc
  exact Koszul.constant_cycle_eq_zero R σ n x hc hx

theorem lower_cycle (n k : ℕ) (x : PolynomialChain R σ (n + 1))
    (hx : x ∈ coefficientLevel R σ (n + 1) (k + 1)) (hcycle : differential b n x = 0) :
    ∃ y, x - differential b (n + 1) y ∈ coefficientLevel R σ (n + 1) k := by
  obtain ⟨y, hydegree, hy⟩ := Koszul.homogeneous_fill R σ n k
    (component R σ (n + 1) (k + 1) x) (top_component_cycle b n (k + 1) x hx hcycle)
    (Koszul.component_idempotent R σ (n + 1) (k + 1) x)
  have hymem : y ∈ coefficientLevel R σ (n + 2) k :=
    hydegree ▸ Koszul.component_mem_coefficientLevel R σ (n + 2) k y
  have herr := leading_error b (n + 1) k y hymem
  have htop := Koszul.sub_top_component_mem R σ (n + 1) k x hx
  refine ⟨-y, ?_⟩
  have h := (coefficientLevel R σ (n + 1) k).add_mem htop herr
  rw [hy] at h
  convert h using 1
  simp only [map_neg]
  abel

theorem exact (n : ℕ) : Function.Exact (differential b (n + 1)) (differential b n) := by
  apply FilteredExactness.exact _ _ (differential_comp_differential b n)
    (coefficientLevel R σ (n + 1)) (Koszul.coefficientLevel_exhaustive R σ (n + 1))
  · intro x hx hc
    rw [constant_cycle_eq_zero b n x hx hc]
    exact Submodule.zero_mem _
  · exact lower_cycle b n

include b

/-- Every positive-degree regular-coefficient CE cycle has a boundary preimage. -/
theorem fill (n : ℕ) (x : Chain R L (Enveloping.Regular R L) (n + 1))
    (hx : Coefficients.differential R L (Enveloping.Regular R L) n x = 0) :
    ∃ y, Coefficients.differential R L (Enveloping.Regular R L) (n + 1) y = x := by
  have hc : differential b n (chains b (n + 1) x) = 0 := by
    rw [differential_chains, hx, map_zero]
  obtain ⟨y, hy⟩ := (exact b n _).mp hc
  refine ⟨(chains b (n + 2)).symm y, ?_⟩
  apply (chains b (n + 1)).injective
  rw [← differential_chains, LinearEquiv.apply_symm_apply, hy]

theorem exactAt (n : ℕ) (hn : n ≠ 0) :
    (complex R L (Enveloping.Regular R L)).ExactAt n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x, ((complex R L (Enveloping.Regular R L)).d (k + 1) k).hom x = 0 →
    ∃ y, ((complex R L (Enveloping.Regular R L)).d (k + 2) (k + 1)).hom y = x
  have hd : (complex R L (Enveloping.Regular R L)).d (k + 2) (k + 1) =
      ModuleCat.ofHom (Coefficients.differential R L (Enveloping.Regular R L) (k + 1)) :=
    complex_d R L (Enveloping.Regular R L) (k + 1)
  rw [complex_d, hd]
  exact fill b k

theorem homology_isZero (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (homology R L (Enveloping.Regular R L) n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (exactAt b n hn)

end Parafree.Homology.Coefficients.PBWCoordinates

namespace Parafree.Homology.Coefficients.Enveloping

open Module CategoryTheory
open Parafree.Linear.ExteriorTensor (Chain)

universe u
variable (R L : Type u) [CommRing R] [LieRing L] [LieAlgebra R L] [Module.Free R L]

/-- Basis-free interface to the regular-coefficient filling theorem. -/
theorem fill (n : ℕ) (x : Chain R L (Regular R L) (n + 1))
    (hx : differential R L (Regular R L) n x = 0) :
    ∃ y, differential R L (Regular R L) (n + 1) y = x := by
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  exact PBWCoordinates.fill (Module.Free.chooseBasis R L) n x hx

theorem exactAt (n : ℕ) (hn : n ≠ 0) : (complex R L (Regular R L)).ExactAt n := by
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  exact PBWCoordinates.exactAt (Module.Free.chooseBasis R L) n hn

theorem homology_isZero (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (homology R L (Regular R L) n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (exactAt R L n hn)

/-- The actual augmentation sequence now supplies an unconditional positive-degree
dimension shift for a Lie algebra free as a module. -/
def augmentationHomologyEquiv (n : ℕ) :
    Homology R L (ideal R L) (n + 1) ≃ₗ[R]
      LieRings.Homological.LieHomology.Homology (R := R) (L := L) (n + 2) :=
  (dimensionShift (sequence_shortExact R L) (n + 1)
    (homology_isZero R L (n + 2) (by omega))
    (homology_isZero R L (n + 1) (by omega))).symm.trans
      (trivialHomologyEquiv R L (n + 2))

end Parafree.Homology.Coefficients.Enveloping
