import Parafree.TheoremB.AuxiliaryCoefficients
import Parafree.Homology.Countable
import Parafree.Linear.CountableDimension

/-! The manuscript's third-homology candidates, in the actual CE complex.
This module establishes the cycles and weights, not their independence. -/
noncomputable section
namespace Parafree.TheoremB.Auxiliary
open LieRings.Homological.LieHomology
open Parafree.Lie.PolynomialSolvable.Algebra

abbrev K := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def triple (i j k : ℕ) : ⋀[K]^3 GmodFive :=
  exteriorPower.ιMulti K 3 ![M K (-9*1) i,M K (-9*1) j,M K (-9*1) k]

theorem triple_cycle (i j k : ℕ) : differential K GmodFive 2 (triple i j k) = 0 := by
  apply Subtype.ext
  simpa only [triple, M_lie, map_zero, zero_mul, neg_zero, add_zero, sub_zero,
    Submodule.coe_zero] using
    differential_two_ιMulti_coe K GmodFive (M K (-9*1) i) (M K (-9*1) j) (M K (-9*1) k)

theorem triple_weight (i j k : ℕ) :
    adExterior K GmodFive (T K (-9*1)) (triple i j k : ExteriorAlgebra K GmodFive) =
      ((i:K)+(j:K)+(k:K)-3) • (triple i j k : ExteriorAlgebra K GmodFive) := by
  simp only [triple, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.tail_cons, Matrix.cons_val_fin_one,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, adExterior_mul, adExterior_ι,
    T_M, map_smul, smul_mul_assoc, mul_smul_comm, mul_add]
  module

/-- The precise cycles listed in the manuscript, as elements of the kernel. -/
def manuscriptCycle (j : ℕ) : Parafree.Homology.Concrete.Cycles K GmodFive 2 :=
  ⟨triple (5*j) (5*j+1) (5*j+2),triple_cycle _ _ _⟩

theorem manuscriptCycle_weight_zero (j : ℕ) :
    adExterior K GmodFive (T K (-9*1))
      (manuscriptCycle j : ExteriorAlgebra K GmodFive) = 0 := by
  change adExterior K GmodFive (T K (-9*1))
    (triple (5*j) (5*j+1) (5*j+2) : ExteriorAlgebra K GmodFive) = 0
  rw [triple_weight]
  have hc : ((5*j:ℕ):K) + ((5*j+1:ℕ):K) + ((5*j+2:ℕ):K) - 3 = 0 := by
    push_cast
    rw [show (5:K) = 0 by decide]
    ring
  rw [hc, zero_smul]

/-- The corresponding classes in the library's actual third CE homology. -/
def manuscriptClass (j : ℕ) : Homology (R := K) (L := GmodFive) 3 :=
  Parafree.Homology.Concrete.homologyClass K GmodFive 2 (manuscriptCycle j)

instance GmodFive_countable : Countable GmodFive := by
  letI : Countable (Polynomial K) := by
    have hs := (Polynomial.basisMonomials K).repr.injective
    exact hs.countable
  exact (Parafree.Lie.PolynomialSolvable.Algebra.coordinates (R := K) (k := -9*1)).injective.countable

instance homologyThree_countable : Countable (Homology (R := K) (L := GmodFive) 3) :=
  Parafree.Homology.homology_countable K GmodFive 2

/-- For Theorem B's abstract isomorphism type, independence of these classes
suffices: countability supplies the matching upper dimension bound. -/
def homologyThreeEquivOfIndependent (h : LinearIndependent K manuscriptClass) :
    Homology (R := K) (L := GmodFive) 3 ≃ₗ[K] (ℕ →₀ K) :=
  Parafree.Linear.countableInfiniteDimensionalEquiv K _ (by
    intro hf
    letI := hf
    haveI := h.finite
    exact not_finite ℕ)

end Parafree.TheoremB.Auxiliary
