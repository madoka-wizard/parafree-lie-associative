import Parafree.Upstream.Koszul.Complex
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Regularity of polynomial variables

Distinct variables form a weakly regular sequence over any commutative ring.
The proof uses coefficients of monomials, so it works in positive characteristic,
over rings with zero divisors, and for an arbitrary ambient set of variables.
-/

namespace Parafree.Homology.Koszul

open MvPolynomial RingTheory.Sequence

variable {R σ : Type*} [CommRing R]

/-- A variable outside a set of variables acts injectively modulo their ideal. -/
theorem mem_span_X_of_mul_mem {s : Set σ} {i : σ} (hi : i ∉ s)
    {p : MvPolynomial σ R} (hp : X i * p ∈ Ideal.span (X '' s)) :
    p ∈ Ideal.span (X '' s) := by
  classical
  rw [mem_ideal_span_X_image] at hp ⊢
  intro m hm
  have hm' : Finsupp.single i 1 + m ∈ (X i * p).support := by
    simpa only [mem_support_iff, coeff_X_mul] using hm
  obtain ⟨j, hj, hmj⟩ := hp _ hm'
  refine ⟨j, hj, ?_⟩
  have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
  simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij.symm, zero_add] using hmj

theorem isSMulRegular_X_quotient_span {s : Set σ} {i : σ} (hi : i ∉ s) :
    IsSMulRegular (MvPolynomial σ R ⧸ Ideal.span (X (R := R) '' s)) (X (R := R) i) := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro p hp
  exact mem_span_X_of_mul_mem hi hp

theorem ofList_map_X (xs : List σ) :
    Ideal.ofList (xs.map (X (R := R))) = Ideal.span (X '' {i | i ∈ xs}) := by
  apply congrArg Ideal.span
  ext p
  simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_image]

/-- Every finite list of distinct variables is weakly regular, without a
Noetherian, domain, field, finite-rank, or nontriviality assumption. -/
theorem variables_weaklyRegular (xs : List σ) (hxs : xs.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (xs.map (X (R := R))) := by
  constructor
  intro i hi
  have hi' : i < xs.length := by simpa only [List.length_map] using hi
  have hnot : xs[i] ∉ xs.take i := by
    intro hmem
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
    have hj' : j < i := lt_of_lt_of_le hj (List.length_take_le i xs)
    simp only [List.getElem_take] at heq
    have hji := hxs.getElem_inj_iff.mp heq
    omega
  rw [← List.map_take, ofList_map_X, Ideal.smul_eq_mul, Ideal.mul_top]
  simpa only [List.getElem_map] using
    (isSMulRegular_X_quotient_span (R := R) (s := {j | j ∈ xs.take i}) hnot)

/-- The polynomial Koszul complex on any finite list of distinct variables is
exact in every positive degree. -/
theorem variables_exactAt (xs : List σ) (hxs : xs.Nodup) (n : ℕ) (hn : n ≠ 0) :
    (koszulComplex.ofList (xs.map (X (R := R)))).ExactAt n :=
  koszulComplex.exactAt_of_isWeaklyRegular _ (variables_weaklyRegular xs hxs) n hn

end Parafree.Homology.Koszul
