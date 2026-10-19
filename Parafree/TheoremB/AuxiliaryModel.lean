import Parafree.TheoremB.AuxiliaryLift

/-! The generators of the explicit auxiliary algebra satisfy the original
relators, and the weight change of generators recovers its coordinate basis. -/
noncomputable section
namespace Parafree.TheoremB.Auxiliary
open Parafree.Lie.PolynomialSolvable
open Parafree.Lie.PolynomialSolvable.Algebra
variable {R : Type*} [CommRing R] (q : R) (hq : (6:R)*q = 1)

def a₀ : G q := q • ((3:R) • S R (-9*q) + (2:R) • E R (-9*q) + M R (-9*q) 0)

include hq in
@[simp] theorem weight_s : WeightRelations.s (T R (-9*q)) (a₀ q) = S R (-9*q) := by
  calc
    _ = (6*q) • S R (-9*q) := by
      simp [WeightRelations.s, w, a₀, lie_smul, lie_add, lie_sub,
        ← Int.cast_smul_eq_zsmul R]
      module
    _ = _ := by rw [hq, one_smul]

include hq in
@[simp] theorem weight_e : WeightRelations.e (T R (-9*q)) (a₀ q) = E R (-9*q) := by
  calc
    _ = (6*q) • E R (-9*q) := by
      simp [WeightRelations.e, a₀, lie_smul, lie_add]
      module
    _ = _ := by rw [hq, one_smul]

include hq in
@[simp] theorem weight_m : WeightRelations.m (T R (-9*q)) (a₀ q) = M R (-9*q) 0 := by
  calc
    _ = (6*q) • M R (-9*q) 0 := by
      simp [WeightRelations.m, w, a₀, lie_smul, lie_add, lie_sub,
        ← Int.cast_smul_eq_zsmul R]
      module
    _ = _ := by rw [hq, one_smul]

include hq in
theorem f₁_zero : f₁ (T R (-9*q)) (a₀ q) = 0 := by
  have h := WeightRelations.s_weight_error (T R (-9*q)) (a₀ q)
  rw [weight_s q hq, T_S, sub_self, eq_comm, neg_eq_zero] at h
  exact h

include hq in
theorem f₂_zero : f₂ (T R (-9*q)) (a₀ q) = 0 := by
  have h := WeightRelations.relator_expansion (T R (-9*q)) (a₀ q)
  rw [weight_s q hq, weight_e q hq, weight_m q hq] at h
  have hc : (2:R)*(-9*q) + 3 = 0 := by linear_combination -3*hq
  have hr : (2:ℤ) • ⁅E R (-9*q),M R (-9*q) 0⁆ +
      (3:ℤ) • ⁅S R (-9*q),⁅S R (-9*q),M R (-9*q) 0⁆⁆ = 0 := by
    simp only [E_M, S_M, ← Int.cast_smul_eq_zsmul R, Int.cast_ofNat, smul_smul]
    rw [← add_smul, hc, zero_smul]
  rw [S_E, hr, S_M, M_lie, smul_zero, smul_zero, sub_zero, sub_zero] at h
  apply six_injective q hq
  apply two_injective q hq
  simpa only [smul_smul, smul_zero] using h

end Parafree.TheoremB.Auxiliary
