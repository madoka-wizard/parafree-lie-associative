import Mathlib.Tactic

/-! Finite denominator cancellation in a saturated descending filtration.
The recursion is Horner evaluation of a finite family. It replaces the choice
of compatible bases in the injectivity proof for divided filtrations. -/

namespace Parafree.Linear.DividedFiltration

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Multiplication by the common denominator, recorded without fractions. -/
def numerator (p : R) (x : ℕ → M) : ℕ → M
  | 0 => x 0
  | n + 1 => p • numerator p x n + x (n + 1)

@[simp] theorem numerator_zero (p : R) (x : ℕ → M) : numerator p x 0 = x 0 := rfl
@[simp] theorem numerator_succ (p : R) (x : ℕ → M) (n : ℕ) :
    numerator p x (n + 1) = p • numerator p x n + x (n + 1) := rfl

theorem numerator_sub_smul (p : R) (x y : ℕ → M) (n : ℕ) :
    numerator p (fun j => x j - p • y j) n =
      numerator p x n - p • numerator p y n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [numerator_succ, ih, smul_add, smul_sub]; abel

variable (E : ℕ → Submodule R M) (p : R)

/-- Each submodule is saturated for multiplication by the chosen denominator. -/
def Saturated : Prop := ∀ n x, p • x ∈ E n → x ∈ E n

/-- Descending cancellation: a relation at the largest common denominator
forces each prefix into the next filtration term. -/
theorem numerator_mem (hE : Antitone E) (hs : Saturated E p)
    (x : ℕ → M) (n : ℕ) (hx : ∀ j ≤ n, x j ∈ E j)
    (hn : numerator p x n ∈ E (n + 1)) :
    ∀ j ≤ n, numerator p x j ∈ E (j + 1) := by
  induction n with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact hn
  | succ n ih =>
    have hprev : numerator p x n ∈ E (n + 1) := by
      apply hs (n + 1)
      have h := (E (n + 1)).sub_mem (hE (by omega : n + 1 ≤ n + 1 + 1) hn)
        (hx (n + 1) le_rfl)
      simpa only [numerator_succ, add_sub_cancel_right] using h
    intro j hj
    rcases Nat.eq_or_lt_of_le hj with rfl | hj
    · exact hn
    · exact ih (fun k hk => hx k (by omega)) hprev j (by omega)

/-- Every coefficient of a zero divided sum vanishes in its graded reduction. -/
theorem term_decomposition (hE : Antitone E) (hs : Saturated E p)
    (x : ℕ → M) (n : ℕ) (hx : ∀ j ≤ n, x j ∈ E j)
    (hn : numerator p x n = 0) (j : ℕ) (hj : j ≤ n) :
    ∃ a ∈ E (j + 1), ∃ b ∈ E j, x j = a + p • b := by
  have hprefix := numerator_mem E p hE hs x n hx (hn ▸ (E (n + 1)).zero_mem)
  cases j with
  | zero => exact ⟨x 0, hprefix 0 hj, 0, (E 0).zero_mem, by simp⟩
  | succ j =>
    refine ⟨numerator p x (j + 1), hprefix (j + 1) hj,
      -numerator p x j, (E (j + 1)).neg_mem (hprefix j (by omega)), ?_⟩
    simp only [numerator_succ, smul_neg]
    abel

/-- Injectivity criterion allowing a divisibility witness at the same finite stage.
No basis, finite-rank hypothesis, or completion is used. -/
theorem term_decomposition_of_divisible (hE : Antitone E) (hs : Saturated E p)
    (x y : ℕ → M) (n : ℕ)
    (hx : ∀ j ≤ n, x j ∈ E j) (hy : ∀ j ≤ n, y j ∈ E j)
    (h : numerator p x n = p • numerator p y n) (j : ℕ) (hj : j ≤ n) :
    ∃ a ∈ E (j + 1), ∃ b ∈ E j, x j = a + p • b := by
  have hz : numerator p (fun k => x k - p • y k) n = 0 := by
    rw [numerator_sub_smul, h, sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := term_decomposition E p hE hs
    (fun k => x k - p • y k) n
    (fun k hk => (E k).sub_mem (hx k hk) ((E k).smul_mem p (hy k hk))) hz j hj
  refine ⟨a, ha, b + y j, (E j).add_mem hb (hy j hj), ?_⟩
  rw [smul_add, ← add_assoc, ← hab]
  exact (sub_add_cancel _ _).symm

end Parafree.Linear.DividedFiltration
