import Parafree.Associative.Quotient
import Mathlib.Order.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Arithmetic

/-! Transfinite powers of a two-sided ideal in a possibly noncommutative ring.
The successor is the sum of left and right products; limits are intersections. -/
noncomputable section
namespace Parafree.Associative.TransfinitePowers
open Order
variable {R : Type*} [Ring R]

instance idealSup_isTwoSided (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] :
    (I ⊔ J).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp ha
    rw [add_mul]
    exact Submodule.mem_sup.mpr ⟨x*b, I.mul_mem_right b hx, y*b, J.mul_mem_right b hy, rfl⟩

/-- The symmetric successor operation in the manuscript. -/
def step (I J : TwoSidedIdeal R) : TwoSidedIdeal R :=
  (J.asIdeal * I.asIdeal ⊔ I.asIdeal * J.asIdeal).toTwoSided

@[simp] theorem step_asIdeal (I J : TwoSidedIdeal R) :
    (step I J).asIdeal = J.asIdeal * I.asIdeal ⊔ I.asIdeal * J.asIdeal :=
  Ideal.asIdeal_toTwoSided _

theorem step_le (I J : TwoSidedIdeal R) : step I J ≤ J := by
  intro x hx
  exact (show J.asIdeal * I.asIdeal ⊔ I.asIdeal * J.asIdeal ≤ J.asIdeal from
    sup_le Ideal.mul_le_right Ideal.mul_le_left)
    (show x ∈ J.asIdeal * I.asIdeal ⊔ I.asIdeal * J.asIdeal from Ideal.mem_toTwoSided.mp hx)

def power (I : TwoSidedIdeal R) (α : Ordinal) : TwoSidedIdeal R :=
  transfiniteIterate (I := OrderDual (TwoSidedIdeal R)) (step I) α (⊤ : TwoSidedIdeal R)

@[simp] theorem power_zero (I : TwoSidedIdeal R) : power I 0 = ⊤ :=
  transfiniteIterate_bot (I := OrderDual (TwoSidedIdeal R)) (step I) (⊤ : TwoSidedIdeal R)

theorem power_succ (I : TwoSidedIdeal R) (α : Ordinal) :
    power I (α+1) = step I (power I α) := by
  simpa only [succ_eq_add_one] using
    transfiniteIterate_succ (I := OrderDual (TwoSidedIdeal R)) (step I) (⊤ : TwoSidedIdeal R) α (not_isMax α)

theorem power_limit (I : TwoSidedIdeal R) (α : Ordinal) (hα : IsSuccLimit α) :
    power I α = ⨅ β : Set.Iio α, power I β.val :=
  transfiniteIterate_limit (I := OrderDual (TwoSidedIdeal R)) (step I) (⊤ : TwoSidedIdeal R) α hα

theorem antitone (I : TwoSidedIdeal R) : Antitone (power I) :=
  monotone_transfiniteIterate (I := OrderDual (TwoSidedIdeal R)) (step I) (⊤ : TwoSidedIdeal R) (step_le I)

@[simp] theorem power_nat_asIdeal (I : TwoSidedIdeal R) (n : ℕ) :
    (power I n).asIdeal = I.asIdeal ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, power_zero, Submodule.pow_zero, Ideal.one_eq_top]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ, power_succ, step_asIdeal, ih]
    rw [← Submodule.pow_succ, ← Ideal.IsTwoSided.pow_succ, sup_idem]

/-- A cofinal family computes any limit power. -/
theorem power_limit_cofinal {T : Type*} (I : TwoSidedIdeal R) (α : Ordinal)
    (hα : IsSuccLimit α) (c : T → Ordinal) (hc : ∀ t, c t < α)
    (hcofinal : ∀ β < α, ∃ t, β ≤ c t) : power I α = ⨅ t, power I (c t) := by
  rw [power_limit I α hα]
  apply le_antisymm
  · exact le_iInf (fun t => iInf_le _ (⟨c t, hc t⟩ : Set.Iio α))
  · apply le_iInf
    intro β
    obtain ⟨t,ht⟩ := hcofinal β.val β.property
    exact (iInf_le _ t).trans (antitone I ht)

theorem power_omega_asIdeal (I : TwoSidedIdeal R) :
    (power I Ordinal.omega0).asIdeal = ⨅ n : ℕ, I.asIdeal ^ n := by
  rw [power_limit_cofinal I Ordinal.omega0 Ordinal.isSuccLimit_omega0
    (fun n : ℕ => (n : Ordinal)) Ordinal.natCast_lt_omega0 (by
      intro β hβ
      obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp hβ
      exact ⟨n,le_rfl⟩)]
  ext x
  simp only [TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_iInf, Submodule.mem_iInf]
  exact forall_congr' (fun n => by rw [← power_nat_asIdeal I n]; rfl)

theorem power_add_omega (I : TwoSidedIdeal R) (α : Ordinal) :
    power I (α + Ordinal.omega0) = ⨅ n : ℕ, power I (α + n) := by
  apply power_limit_cofinal I _ (Ordinal.isSuccLimit_add α Ordinal.isSuccLimit_omega0)
  · intro n
    exact (Ordinal.isNormal_add_right α).strictMono (Ordinal.natCast_lt_omega0 n)
  · intro β hβ
    obtain ⟨γ,hγ,hβγ⟩ := (Ordinal.lt_add_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mp hβ
    obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp hγ
    exact ⟨n,hβγ.le⟩

/-- Right multiplication gives a lower bound on every finite tail. -/
theorem right_mul_pow_le (I : TwoSidedIdeal R) (α : Ordinal) (n : ℕ) :
    (power I α).asIdeal * I.asIdeal ^ n ≤ (power I (α+n)).asIdeal := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero, Submodule.pow_zero, Ideal.IsTwoSided.mul_one]; rfl
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, power_succ, step_asIdeal, Submodule.pow_succ,
      ← Ideal.mul_assoc]
    exact (Ideal.mul_mono ih le_rfl).trans le_sup_left

/-- Once a successor does not decrease the ideal, every later power is equal. -/
theorem stable_after (I : TwoSidedIdeal R) (α : Ordinal)
    (hα : power I (α+1) = power I α) :
    ∀ β, α ≤ β → power I β = power I α := by
  have hs : step I (power I α) = power I α := (power_succ I α).symm.trans hα
  intro β
  induction β using SuccOrder.limitRecOn with
  | isMin β hβ =>
    intro h
    have he : α = β := le_antisymm h (hβ.eq_bot ▸ bot_le)
    rw [he]
  | succ β hβ ih =>
    intro h
    obtain hlt | he := h.lt_or_eq
    · have hab : α ≤ β := (lt_succ_iff_of_not_isMax hβ).mp hlt
      simpa only [succ_eq_add_one, power_succ, ih hab] using hs
    · rw [← he]
  | isSuccLimit β hβ ih =>
    intro h
    apply le_antisymm (antitone I h)
    rw [power_limit I β hβ]
    apply le_iInf
    intro γ
    by_cases ha : α ≤ γ.val
    · rw [ih γ.val γ.property ha]
    · exact antitone I (le_of_not_ge ha)

end Parafree.Associative.TransfinitePowers
