import Parafree.Homology.Koszul.ArbitraryRank

/-!
# Homogeneous fillings in the polynomial Koszul complex

The polynomial degree of the coefficients is separate from exterior degree.
Projecting an arbitrary filling to the correct coefficient degree supplies the
bounded filling needed in a filtered PBW argument. No division by a degree is
used, and the base ring and rank are arbitrary.
-/

noncomputable section

namespace Parafree.Homology.Koszul

open Module MvPolynomial

variable (R σ : Type*) [CommRing R]

abbrev PolynomialChain (n : ℕ) := ⋀[Polynomial R σ]^n (σ →₀ Polynomial R σ)

scoped instance polynomialChainModule (n : ℕ) : Module R (PolynomialChain R σ n) :=
  Module.compHom _ (algebraMap R (Polynomial R σ))

scoped instance polynomialChainTower (n : ℕ) :
    IsScalarTower R (Polynomial R σ) (PolynomialChain R σ n) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

theorem homogeneousComponent_monomial (d : σ →₀ ℕ) (r : R) (k : ℕ) :
    homogeneousComponent k (monomial d r) = if k = d.degree then monomial d r else 0 :=
  homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)

/-- Multiplication by a variable raises polynomial degree by one. -/
theorem homogeneousComponent_X_mul (i : σ) (p : Polynomial R σ) (k : ℕ) :
    homogeneousComponent (k + 1) (X i * p) = X i * homogeneousComponent k p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | monomial d r =>
    simp only [X, monomial_mul, one_mul, homogeneousComponent_monomial,
      map_add, Finsupp.degree_single]
    have h : k + 1 = 1 + d.degree ↔ k = d.degree := by omega
    simp only [h]
    split_ifs <;> simp

theorem homogeneousComponent_zero_X_mul (i : σ) (p : Polynomial R σ) :
    homogeneousComponent 0 (X i * p) = 0 := by
  classical
  simp [coeff_X_mul']

variable [LinearOrder σ]

def exteriorBasis (n : ℕ) :
    Basis (Set.powersetCard σ n) (Polynomial R σ) (PolynomialChain R σ n) :=
  Finsupp.basisSingleOne.exteriorPower n

/-- Projection of every coefficient onto one homogeneous polynomial degree. -/
def component (n k : ℕ) : PolynomialChain R σ n →ₗ[R] PolynomialChain R σ n :=
  ((exteriorBasis R σ n).repr.symm.restrictScalars R).toLinearMap.comp
    ((Finsupp.mapRange.linearMap (homogeneousComponent k)).comp
      ((exteriorBasis R σ n).repr.restrictScalars R).toLinearMap)

@[simp] theorem component_repr (n k : ℕ) (x : PolynomialChain R σ n)
    (s : Set.powersetCard σ n) :
    (exteriorBasis R σ n).repr (component R σ n k x) s =
      homogeneousComponent k ((exteriorBasis R σ n).repr x s) := by
  simp [component, Finsupp.mapRange.linearMap]

theorem component_smul_basis (n k : ℕ) (p : Polynomial R σ)
    (s : Set.powersetCard σ n) :
    component R σ n k (p • exteriorBasis R σ n s) =
      homogeneousComponent k p • exteriorBasis R σ n s := by
  classical
  apply (exteriorBasis R σ n).repr.injective
  ext t
  simp only [component_repr, map_smul, Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.single_apply]
  split_ifs <;> simp

theorem component_idempotent (n k : ℕ) (x : PolynomialChain R σ n) :
    component R σ n k (component R σ n k x) = component R σ n k x := by
  apply (exteriorBasis R σ n).repr.injective
  apply Finsupp.ext
  intro s
  simp only [component_repr]
  exact (homogeneousComponent_of_mem (homogeneousComponent_mem k
    ((exteriorBasis R σ n).repr x s))).trans (if_pos rfl)

def eraseIndex {n : ℕ} (s : Set.powersetCard σ (n + 1)) (i : Fin (n + 1)) :
    Set.powersetCard σ n :=
  Set.powersetCard.ofFinEmbEquiv
    ((Fin.succAboveOrderEmb i).trans (Set.powersetCard.ofFinEmbEquiv.symm s))

theorem differential_basis (n : ℕ) (s : Set.powersetCard σ (n + 1)) :
    koszulComplex.d (variableMap R σ) n (exteriorBasis R σ (n + 1) s) =
      ∑ i : Fin (n + 1),
        ((-1 : Polynomial R σ) ^ (i : ℕ) * X (Set.powersetCard.ofFinEmbEquiv.symm s i)) •
          exteriorBasis R σ n (eraseIndex σ s i) := by
  simp only [exteriorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    koszulComplex.d, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    koszulComplex.dAlternating_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  · simp [variableMap, Finsupp.coe_basisSingleOne]
  · simp only [eraseIndex, Equiv.symm_apply_apply]
    rfl

theorem component_differential (n k : ℕ) (x : PolynomialChain R σ (n + 1)) :
    component R σ n (k + 1) (koszulComplex.d (variableMap R σ) n x) =
      koszulComplex.d (variableMap R σ) n (component R σ (n + 1) k x) := by
  classical
  conv_lhs => rw [← (exteriorBasis R σ (n + 1)).linearCombination_repr x]
  conv_rhs => rw [← (exteriorBasis R σ (n + 1)).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    component_smul_basis, differential_basis, Finset.smul_sum,
    smul_smul]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hsign : (-1 : Polynomial R σ) ^ (i : ℕ) = C ((-1 : R) ^ (i : ℕ)) := by simp
  rw [hsign]
  have hperm (p : Polynomial R σ) (r : R) (j : σ) :
      p * (C r * X j) = C r * (X j * p) := by ring
  rw [hperm, homogeneousComponent_C_mul, homogeneousComponent_X_mul]
  ring

theorem component_zero_differential (n : ℕ) (x : PolynomialChain R σ (n + 1)) :
    component R σ n 0 (koszulComplex.d (variableMap R σ) n x) = 0 := by
  classical
  rw [← (exteriorBasis R σ (n + 1)).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    differential_basis, Finset.smul_sum, smul_smul, component_smul_basis]
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro i _
  have hsign : (-1 : Polynomial R σ) ^ (i : ℕ) = C ((-1 : R) ^ (i : ℕ)) := by simp
  rw [hsign]
  have hperm (p : Polynomial R σ) (r : R) (j : σ) :
      p * (C r * X j) = C r * (X j * p) := by ring
  rw [hperm, homogeneousComponent_C_mul, homogeneousComponent_zero_X_mul,
    mul_zero, zero_smul]

/-- A positive-degree cycle has no constant coefficient component. -/
theorem component_zero_of_cycle (n : ℕ) (x : PolynomialChain R σ (n + 1))
    (hx : koszulComplex.d (variableMap R σ) n x = 0) :
    component R σ (n + 1) 0 x = 0 := by
  obtain ⟨y, rfl⟩ := fill R σ n x hx
  exact component_zero_differential R σ (n + 1) y

/-- The coefficient filtration, without adding the exterior degree. -/
def coefficientLevel (n k : ℕ) : Submodule R (PolynomialChain R σ n) :=
  ⨅ s, (MvPolynomial.restrictTotalDegree σ R k).comap
    (((exteriorBasis R σ n).coord s).restrictScalars R)

theorem mem_coefficientLevel (n k : ℕ) (x : PolynomialChain R σ n) :
    x ∈ coefficientLevel R σ n k ↔
      ∀ s, ((exteriorBasis R σ n).repr x s).totalDegree ≤ k := by
  simp [coefficientLevel, MvPolynomial.mem_restrictTotalDegree, Basis.coord_apply]

theorem smul_basis_mem_coefficientLevel (n k : ℕ) (p : Polynomial R σ)
    (hp : p.totalDegree ≤ k) (s : Set.powersetCard σ n) :
    p • exteriorBasis R σ n s ∈ coefficientLevel R σ n k := by
  classical
  rw [mem_coefficientLevel]
  intro t
  simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_apply]
  split_ifs
  · exact hp
  · simp

theorem component_mem_coefficientLevel (n k : ℕ) (x : PolynomialChain R σ n) :
    component R σ n k x ∈ coefficientLevel R σ n k := by
  rw [mem_coefficientLevel]
  intro s
  rw [component_repr]
  exact (homogeneousComponent_isHomogeneous k _).totalDegree_le

theorem coefficientLevel_mono (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    coefficientLevel R σ n k ≤ coefficientLevel R σ n l := by
  intro x hx
  rw [mem_coefficientLevel] at hx ⊢
  exact fun s => (hx s).trans h

theorem component_eq_zero_of_mem (n k l : ℕ) (x : PolynomialChain R σ n)
    (hx : x ∈ coefficientLevel R σ n k) (hkl : k < l) : component R σ n l x = 0 := by
  apply (exteriorBasis R σ n).repr.injective
  apply Finsupp.ext
  intro s
  simp only [component_repr, map_zero, Finsupp.zero_apply]
  exact homogeneousComponent_eq_zero l _
    (((mem_coefficientLevel R σ n k x).mp hx s).trans_lt hkl)

theorem coefficientLevel_exhaustive (n : ℕ) (x : PolynomialChain R σ n) :
    ∃ k, x ∈ coefficientLevel R σ n k := by
  classical
  let c := (exteriorBasis R σ n).repr x
  refine ⟨c.support.sup (fun s => (c s).totalDegree), ?_⟩
  rw [mem_coefficientLevel]
  intro s
  by_cases hs : s ∈ c.support
  · exact Finset.le_sup (f := fun t => (c t).totalDegree) hs
  · have hz : c s = 0 := Finsupp.notMem_support_iff.mp hs
    change (c s).totalDegree ≤ _
    simp only [hz, totalDegree_zero, Nat.zero_le]

omit [LinearOrder σ] in
theorem sum_homogeneousComponent_of_bound (p : Polynomial R σ) (k : ℕ)
    (hp : p.totalDegree ≤ k) :
    (∑ j ∈ Finset.range (k + 1), homogeneousComponent j p) = p := by
  classical
  calc
    _ = ∑ j ∈ Finset.range (p.totalDegree + 1), homogeneousComponent j p := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hp 1))
      intro j _ hj
      apply homogeneousComponent_eq_zero
      have h : p.totalDegree + 1 ≤ j := by simpa using hj
      omega
    _ = p := sum_homogeneousComponent p

theorem sum_component_of_mem (n k : ℕ) (x : PolynomialChain R σ n)
    (hx : x ∈ coefficientLevel R σ n k) :
    (∑ j ∈ Finset.range (k + 1), component R σ n j x) = x := by
  apply (exteriorBasis R σ n).ext_elem
  intro s
  simp only [map_sum, Finsupp.finset_sum_apply, component_repr]
  exact sum_homogeneousComponent_of_bound R σ _ k ((mem_coefficientLevel R σ n k x).mp hx s)

theorem sub_top_component_mem (n k : ℕ) (x : PolynomialChain R σ n)
    (hx : x ∈ coefficientLevel R σ n (k + 1)) :
    x - component R σ n (k + 1) x ∈ coefficientLevel R σ n k := by
  have h := sum_component_of_mem R σ n (k + 1) x hx
  rw [Finset.sum_range_succ] at h
  rw [← eq_sub_of_add_eq h]
  apply Submodule.sum_mem
  intro j hj
  exact coefficientLevel_mono R σ n (by simpa using hj)
    (component_mem_coefficientLevel R σ n j x)

/-- Constant-coefficient positive-degree cycles are zero. This is the bottom
step in the filtered resolution; it does not use an Euler contraction. -/
theorem constant_cycle_eq_zero (n : ℕ) (x : PolynomialChain R σ (n + 1))
    (hx : koszulComplex.d (variableMap R σ) n x = 0)
    (hdegree : x ∈ coefficientLevel R σ (n + 1) 0) : x = 0 := by
  have h := sum_component_of_mem R σ (n + 1) 0 x hdegree
  simpa only [zero_add, Finset.sum_range_one, component_zero_of_cycle R σ n x hx] using h.symm

/-- A positive-degree homogeneous cycle of coefficient degree `k + 1` has a
filling homogeneous of coefficient degree `k`. -/
theorem homogeneous_fill (n k : ℕ) (x : PolynomialChain R σ (n + 1))
    (hx : koszulComplex.d (variableMap R σ) n x = 0)
    (hdegree : component R σ (n + 1) (k + 1) x = x) :
    ∃ y : PolynomialChain R σ (n + 2),
      component R σ (n + 2) k y = y ∧
        koszulComplex.d (variableMap R σ) (n + 1) y = x := by
  obtain ⟨y, hy⟩ := fill R σ n x hx
  refine ⟨component R σ (n + 2) k y, component_idempotent R σ (n + 2) k y, ?_⟩
  rw [← component_differential, hy, hdegree]

/-- A positive-degree cycle with coefficient degree at most `k + 1` can be
filled with coefficient degree at most `k`. The bound is an actual conclusion,
not an assumption on a chosen preimage. -/
theorem bounded_fill (n k : ℕ) (x : PolynomialChain R σ (n + 1))
    (hx : koszulComplex.d (variableMap R σ) n x = 0)
    (hdegree : x ∈ coefficientLevel R σ (n + 1) (k + 1)) :
    ∃ y : PolynomialChain R σ (n + 2),
      y ∈ coefficientLevel R σ (n + 2) k ∧
        koszulComplex.d (variableMap R σ) (n + 1) y = x := by
  obtain ⟨y, hy⟩ := fill R σ n x hx
  refine ⟨∑ j ∈ Finset.range (k + 1), component R σ (n + 2) j y, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro j hj
    apply coefficientLevel_mono R σ (n + 2) (by simpa using hj)
    exact component_mem_coefficientLevel R σ (n + 2) j y
  · simp only [map_sum, ← component_differential, hy]
    have h := sum_component_of_mem R σ (n + 1) (k + 1) x hdegree
    rw [Finset.sum_range_succ', component_zero_of_cycle R σ n x hx, add_zero] at h
    exact h

end Parafree.Homology.Koszul
