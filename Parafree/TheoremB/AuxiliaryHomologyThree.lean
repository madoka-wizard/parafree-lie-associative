import Parafree.TheoremB.AuxiliaryCycles
import Parafree.Homology.Equivalence
import Parafree.Homology.PolynomialCubic

/-! Countably infinite actual third CE homology of the auxiliary algebra.
Coefficient cocycles separate the manuscript's cycles. Countability gives
an abstract basis; no spanning claim about the particular cycles is needed. -/
noncomputable section
namespace Parafree.TheoremB.Auxiliary
open LieRings.Homological.LieHomology
open Parafree.Linear.PolynomialCubic
open Parafree.Lie.PolynomialSolvable.Algebra
open scoped BigOperators

theorem detector_weight (j : ℕ) : (((15*j+3:ℕ):K)-3) = 0 := by
  push_cast
  rw [show (15:K) = 0 by decide]
  ring

def detector (j : ℕ) : Homology (R := K) (L := GmodFive) 3 →ₗ[K] K :=
  Parafree.Homology.PolynomialCubic.evaluate K (-9*1) (15*j+3) (detector_weight j)

@[simp] theorem detector_class (i j : ℕ) :
    detector i (manuscriptClass j) = if i = j then 1 else 0 := by
  unfold detector Parafree.Homology.PolynomialCubic.evaluate manuscriptClass
  rw [Parafree.Homology.Concrete.evaluate_class]
  change (Parafree.Homology.PolynomialCubic.cochain K (-9*1)
    (triple (5*j) (5*j+1) (5*j+2))).coeff (15*i+3) = _
  rw [triple, Parafree.Homology.PolynomialCubic.cochain_wedge]
  change (value K (Polynomial.X^(5*j)) (Polynomial.X^(5*j+1))
    (Polynomial.X^(5*j+2))).coeff (15*i+3) = _
  rw [value_consecutive]
  have he : 3*(5*j)+3 = 15*j+3 := by omega
  rw [he, Polynomial.coeff_X_pow]
  split_ifs <;> simp_all

/-- Independence holds in actual homology, not just in the space of chains. -/
theorem manuscriptClass_independent : LinearIndependent K manuscriptClass := by
  apply linearIndependent_iff'.mpr
  intro s g hg i hi
  have he := congrArg (detector i) hg
  simpa only [map_sum, map_smul, map_zero, detector_class, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos hi] using he

def modFive_homologyThreeEquiv : Homology (R := K) (L := GmodFive) 3 ≃ₗ[K] (ℕ →₀ K) :=
  homologyThreeEquivOfIndependent manuscriptClass_independent

/-- The same result for the exact two-relator presentation. -/
def presentedModFive_homologyThreeEquiv :
    Homology (R := K) (L := Presented K) 3 ≃ₗ[K] (ℕ →₀ K) :=
  (Parafree.Homology.lieEquivHomology modFiveEquiv 3).trans modFive_homologyThreeEquiv

end Parafree.TheoremB.Auxiliary
