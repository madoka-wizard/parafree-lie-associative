import Parafree.Homology.Coefficients.PBWCoordinates
import Parafree.Homology.Coefficients.PureFormula

/-!
# The leading differential in PBW coordinates

Separate the exterior-bracket contribution from the coefficient actions. In an
ordered exterior basis the latter are the negative Koszul differential, up to
the already proved lower-degree PBW multiplication errors.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.PBWCoordinates

open Module MvPolynomial
open scoped TensorProduct Parafree.Homology.Koszul
open Parafree.Linear.ExteriorTensor (Chain)
open Parafree.Homology.Koszul (Polynomial PolynomialChain exteriorBasis coefficientLevel)

universe u
variable {R L σ : Type u} [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder σ]
  (b : Basis σ R L)

local instance (n : ℕ) : Module R (PolynomialChain R σ n) :=
  Koszul.polynomialChainModule R σ n

-- Use the base-ring action directly when both scalar rings occur in one expression.
local instance (n : ℕ) : SMul R (PolynomialChain R σ n) :=
  ⟨fun r x => (algebraMap R (Polynomial R σ) r) • x⟩

local instance (n : ℕ) : IsScalarTower R (Polynomial R σ) (PolynomialChain R σ n) :=
  Koszul.polynomialChainTower R σ n

theorem chains_tmul_mem (n k : ℕ) (u : ⋀[R]^n L) (m : Enveloping.Regular R L)
    (hm : (coefficients b m).totalDegree ≤ k) :
    chains b n (u ⊗ₜ[R] m) ∈ coefficientLevel R σ n k := by
  classical
  rw [← (b.exteriorPower n).linearCombination_repr u, Finsupp.linearCombination_apply,
    Finsupp.sum, TensorProduct.sum_tmul]
  have hs : chains b n (∑ s ∈ ((b.exteriorPower n).repr u).support,
      (((b.exteriorPower n).repr u s) • b.exteriorPower n s) ⊗ₜ[R] m) =
      ∑ s ∈ ((b.exteriorPower n).repr u).support,
        chains b n ((((b.exteriorPower n).repr u s) • b.exteriorPower n s) ⊗ₜ[R] m) :=
    map_sum (chains b n).toLinearMap.toAddMonoidHom _ _
  rw [hs]
  apply Submodule.sum_mem
  intro s _
  simp only [← TensorProduct.smul_tmul', map_smul, chains_tmul_basis]
  exact Submodule.smul_mem _ _ (Koszul.smul_basis_mem_coefficientLevel R σ n k _ hm s)

theorem coefficients_action_error (x : L) (k : ℕ) (m : Enveloping.Regular R L)
    (hm : (coefficients b m).totalDegree ≤ k) :
    (coefficients b ⁅x, m⁆ - LieRings.PBW.basisPolynomial R L σ b x *
      coefficients b m).totalDegree ≤ k := by
  have h := Parafree.Associative.FilteredPBW.coordinate_left_error_mem b x k
    ((Parafree.Associative.FilteredPBW.mem_polynomialLevel_iff k _).mpr hm)
  rw [Parafree.Associative.FilteredPBW.mem_polynomialLevel_iff] at h
  simpa only [coefficients, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Enveloping.equiv_lie] using h

theorem basis_erase {n : ℕ} (s : Set.powersetCard σ (n + 1)) (i : Fin (n + 1)) :
    exteriorPower.ιMulti R n (i.removeNth (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) =
      b.exteriorPower n (Koszul.eraseIndex σ s i) := by
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    Koszul.eraseIndex, Equiv.symm_apply_apply]
  rfl

theorem koszul_smul_basis (n : ℕ) (p : Polynomial R σ) (s : Set.powersetCard σ (n + 1)) :
    koszulComplex.d (Koszul.variableMap R σ) n (p • exteriorBasis R σ (n + 1) s) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) •
        ((X (Set.powersetCard.ofFinEmbEquiv.symm s i) * p) •
          exteriorBasis R σ n (Koszul.eraseIndex σ s i)) : PolynomialChain R σ n) := by
  rw [map_smul, Koszul.differential_basis, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← IsScalarTower.algebraMap_smul (Polynomial R σ) ((-1 : R) ^ (i : ℕ))]
  simp only [map_pow, map_neg, map_one, smul_smul]
  congr 1
  ring

theorem differential_smul_basis (n : ℕ) (p : Polynomial R σ)
    (s : Set.powersetCard σ (n + 1)) :
    differential b n (p • exteriorBasis R σ (n + 1) s) =
      chains b n (LieRings.Homological.LieHomology.differential R L n
        (b.exteriorPower (n + 1) s) ⊗ₜ[R] (coefficients b).symm p) -
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) •
        (coefficients b ⁅b (Set.powersetCard.ofFinEmbEquiv.symm s i), (coefficients b).symm p⁆ •
          exteriorBasis R σ n (Koszul.eraseIndex σ s i)) : PolynomialChain R σ n) := by
  have hc := chains_tmul_basis b (n + 1) ((coefficients b).symm p) s
  rw [LinearEquiv.apply_symm_apply] at hc
  rw [← hc, differential_chains]
  have he : b.exteriorPower (n + 1) s =
      exteriorPower.ιMulti R (n + 1) (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  rw [he]
  change chains b n (Coefficients.differential R L (Enveloping.Regular R L) n
    (pure R L (Enveloping.Regular R L) (n + 1)
      (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) ((coefficients b).symm p))) = _
  rw [differential_pure_separation, map_sub, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  congr 1
  simp only [pure, basis_erase, chains_tmul_basis, Function.comp_apply]

theorem leading_error_smul_basis (n k : ℕ) (p : Polynomial R σ)
    (hp : p.totalDegree ≤ k) (s : Set.powersetCard σ (n + 1)) :
    differential b n (p • exteriorBasis R σ (n + 1) s) +
      koszulComplex.d (Koszul.variableMap R σ) n (p • exteriorBasis R σ (n + 1) s) ∈
        coefficientLevel R σ n k := by
  rw [differential_smul_basis, koszul_smul_basis]
  have hbr := chains_tmul_mem b n k
    (LieRings.Homological.LieHomology.differential R L n (b.exteriorPower (n + 1) s))
    ((coefficients b).symm p) (by simpa using hp)
  have herr : (∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) •
      ((coefficients b ⁅b (Set.powersetCard.ofFinEmbEquiv.symm s i), (coefficients b).symm p⁆ -
        X (Set.powersetCard.ofFinEmbEquiv.symm s i) * p) •
          exteriorBasis R σ n (Koszul.eraseIndex σ s i)) : PolynomialChain R σ n)) ∈
      coefficientLevel R σ n k := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Koszul.smul_basis_mem_coefficientLevel
    simpa only [LieRings.PBW.basisPolynomial_basis, LinearEquiv.apply_symm_apply] using
      coefficients_action_error b (b (Set.powersetCard.ofFinEmbEquiv.symm s i)) k
        ((coefficients b).symm p) (by simpa using hp)
  have h := (coefficientLevel R σ n k).sub_mem hbr herr
  simp only [sub_smul, smul_sub, Finset.sum_sub_distrib] at h
  convert h using 1; abel

/-- The principal CE differential is negative Koszul contraction. Its error
preserves polynomial coefficient degree, in every exterior degree. -/
theorem leading_error (n k : ℕ) (x : PolynomialChain R σ (n + 1))
    (hx : x ∈ coefficientLevel R σ (n + 1) k) :
    differential b n x + koszulComplex.d (Koszul.variableMap R σ) n x ∈
      coefficientLevel R σ n k := by
  classical
  conv => arg 2; rw [← (exteriorBasis R σ (n + 1)).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, ← Finset.sum_add_distrib]
  apply Submodule.sum_mem
  intro s _
  apply leading_error_smul_basis b n k ((exteriorBasis R σ (n + 1)).repr x s)
  exact (Koszul.mem_coefficientLevel R σ (n + 1) k x).mp hx s

end Parafree.Homology.Coefficients.PBWCoordinates
