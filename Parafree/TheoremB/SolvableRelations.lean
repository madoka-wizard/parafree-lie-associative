import Parafree.TheoremB.Identities
import Parafree.Lie.DerivationOrbit

/-! The finite solvable relations imply all of the polynomial-orbit bracket
relations used in the auxiliary algebra of Theorem B. -/

namespace Parafree.TheoremB.SolvableRelations

variable {L : Type*} [LieRing L]

def monomial (s m : L) (n : ℕ) : L := Parafree.Lie.DerivationOrbit.orbit (ad s) m n

@[simp] theorem monomial_zero (s m : L) : monomial s m 0 = m := rfl
@[simp] theorem monomial_succ (s m : L) (n : ℕ) :
    monomial s m (n + 1) = ⁅s, monomial s m n⁆ := rfl

variable (s e m : L) (hse : ⁅s, e⁆ = 0)
  (hem : (2 : ℤ) • ⁅e, m⁆ = (-3 : ℤ) • ⁅s, ⁅s, m⁆⁆)

include hse in
private theorem action_commute (z : L) : ad e (ad s z) = ad s (ad e z) := by
  have hes : ⁅e, s⁆ = 0 := by rw [← lie_skew, hse, neg_zero]
  simp only [ad_apply, leibniz_lie e s z, hes, zero_lie, zero_add]

include hse hem in
theorem e_monomial (n : ℕ) :
    (2 : ℤ) • ⁅e, monomial s m n⁆ = (-3 : ℤ) • monomial s m (n + 2) :=
  Parafree.Lie.DerivationOrbit.action (ad s) (ad e) m (action_commute s e hse) hem n

include hse hem in
theorem monomial_commute
    (h6 : Function.Injective (fun z : L => (6 : ℤ) • z))
    (hmm : ⁅m, ⁅s, m⁆⁆ = 0) (i j : ℕ) : ⁅monomial s m i, monomial s m j⁆ = 0 :=
  Parafree.Lie.DerivationOrbit.pairwise_commute (ad s) (ad e) m
    (action_commute s e hse) hem h6 hmm i j

theorem t_monomial (t s m : L) (hts : ⁅t, s⁆ = s) (htm : ⁅t, m⁆ = -m) (n : ℕ) :
    ⁅t, monomial s m n⁆ = ((n : ℤ) - 1) • monomial s m n := by
  apply Parafree.Lie.DerivationOrbit.weight (ad s) m (ad t) (-1)
  · intro z
    simp only [ad_apply, leibniz_lie t s z, hts]
    exact add_comm _ _
  · simpa only [ad_apply, neg_one_smul] using htm

end Parafree.TheoremB.SolvableRelations
