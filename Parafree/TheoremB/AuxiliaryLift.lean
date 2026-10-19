import Parafree.Lie.PolynomialSolvableBasis
import Parafree.Lie.ScalarExtension
import Parafree.TheoremB.WeightRelations

/-! A universal map from the explicit auxiliary algebra to any solution of
Theorem B's two relators, over any ring in which six is invertible. -/
noncomputable section
namespace Parafree.TheoremB.Auxiliary
open Parafree.Lie.PolynomialSolvable
open WeightRelations SolvableRelations
variable {R : Type*} [CommRing R] (q : R) (hq : (6:R)*q = 1)
variable {L : Type*} [LieRing L] [LieAlgebra R L]

include hq in
theorem two_injective : Function.Injective (fun z : L => (2:ℤ) • z) :=
  Parafree.Lie.ScalarExtension.int_smul_injective_of_mul_eq_one R 2 (3*q)
    (by norm_num; linear_combination hq) L

include hq in
theorem three_injective : Function.Injective (fun z : L => (3:ℤ) • z) :=
  Parafree.Lie.ScalarExtension.int_smul_injective_of_mul_eq_one R 3 (2*q)
    (by norm_num; linear_combination hq) L

include hq in
theorem six_injective : Function.Injective (fun z : L => (6:ℤ) • z) :=
  Parafree.Lie.ScalarExtension.int_smul_injective_of_mul_eq_one R 6 q
    (by simpa using hq) L

abbrev G := Parafree.Lie.PolynomialSolvable.Algebra R (-9*q)

include hq in
private theorem two_coefficient : (2:R)*(-9*q) = -3 := by linear_combination -3*hq

/-- The polynomial orbit construction, including every bracket relation. -/
def orbitLiftData (t s e m : L) (hse : ⁅s,e⁆ = 0)
    (hem : (2:ℤ) • ⁅e,m⁆ = (-3:ℤ) • ⁅s,⁅s,m⁆⁆)
    (hmm : ⁅m,⁅s,m⁆⁆ = 0) (hts : ⁅t,s⁆ = s)
    (hte : ⁅t,e⁆ = (2:ℤ) • e) (htm : ⁅t,m⁆ = -m) :
    LiftData (R := R) (k := -9*q) (L := L) := by
  refine liftDataOfBasis t s e (monomial s m)
    (monomial_commute s e m hse hem (six_injective q hq) hmm)
    (fun _ => rfl) ?_ ?_ hse hts ?_
  · intro n
    apply two_injective q hq
    change (2:ℤ) • ⁅e,monomial s m n⁆ = (2:ℤ) • ((-9*q) • monomial s m (n+2))
    rw [e_monomial s e m hse hem]
    simp only [← Int.cast_smul_eq_zsmul R, smul_smul]
    norm_num only [Int.cast_ofNat, Int.cast_neg]
    rw [two_coefficient q hq]
  · intro n
    rw [t_monomial t s m hts htm]
    simp only [← Int.cast_smul_eq_zsmul R, Int.cast_sub, Int.cast_natCast, Int.cast_one]
  · simpa only [← Int.cast_smul_eq_zsmul R, Int.cast_ofNat] using hte

/-- The explicit reverse map needed for the presentation isomorphism. -/
def liftData (t a : L) (hf₁ : f₁ t a = 0) (hf₂ : f₂ t a = 0) :
    LiftData (R := R) (k := -9*q) (L := L) := by
  have hrs := solvable_relations t a
    (two_injective q hq) (three_injective q hq) hf₁ hf₂
  apply orbitLiftData q hq t (s t a) (e t a) (m t a) hrs.1
    (by simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hrs.2.1) hrs.2.2
  · have h := s_weight_error t a
    rw [hf₁, neg_zero, sub_eq_zero] at h
    exact h
  · have h := e_weight_error t a
    rw [hf₁, sub_eq_zero] at h
    exact h
  · have h := m_weight_error t a
    rw [hf₁] at h
    exact eq_neg_of_add_eq_zero_left h

end Parafree.TheoremB.Auxiliary
