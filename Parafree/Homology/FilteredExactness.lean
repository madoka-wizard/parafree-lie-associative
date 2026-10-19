import Mathlib.Algebra.Exact

/-! Finite descent from leading-term lifts to exactness.

This is the termination argument for a filtered resolution: every cycle has a
finite filtration bound, and subtracting a lifted leading boundary decreases that
bound. No infinite sum, completion, bounded dimension, or division is used.
The filtration-zero case is exposed separately so the lemma also applies to an
augmented complex with nonzero constants.
-/

namespace Parafree.Homology.FilteredExactness

variable {R A B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
variable (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hfg : g.comp f = 0)
  (F : ℕ → Submodule R B)

include hfg

/-- Fill a cycle by a finite number of strictly descending corrections. -/
theorem cycle_mem_range
    (base : ∀ b ∈ F 0, g b = 0 → b ∈ LinearMap.range f)
    (lower : ∀ n b, b ∈ F (n + 1) → g b = 0 → ∃ a, b - f a ∈ F n)
    (n : ℕ) {b : B} (hb : b ∈ F n) (hg : g b = 0) : b ∈ LinearMap.range f := by
  induction n generalizing b with
  | zero => exact base b hb hg
  | succ n ih =>
    obtain ⟨a, ha⟩ := lower n b hb hg
    have hz : g (b - f a) = 0 := by
      rw [map_sub, hg, show g (f a) = 0 from LinearMap.congr_fun hfg a, sub_self]
    obtain ⟨a', ha'⟩ := ih ha hz
    refine ⟨a' + a, ?_⟩
    rw [map_add, ha', sub_add_cancel]

/-- Exhaustiveness and leading-term lifts imply exactness of a pair of linear maps. -/
theorem exact
    (exhaustive : ∀ b : B, ∃ n, b ∈ F n)
    (base : ∀ b ∈ F 0, g b = 0 → b ∈ LinearMap.range f)
    (lower : ∀ n b, b ∈ F (n + 1) → g b = 0 → ∃ a, b - f a ∈ F n) :
    Function.Exact f g := by
  intro b
  constructor
  · intro hb
    obtain ⟨n, hn⟩ := exhaustive b
    exact cycle_mem_range f g hfg F base lower n hn hb
  · rintro ⟨a, rfl⟩
    exact LinearMap.congr_fun hfg a

/-- A common positive-degree case: the zeroth filtered piece is zero. -/
theorem exact_of_zero_base
    (exhaustive : ∀ b : B, ∃ n, b ∈ F n) (hzero : F 0 = ⊥)
    (lower : ∀ n b, b ∈ F (n + 1) → g b = 0 → ∃ a, b - f a ∈ F n) :
    Function.Exact f g :=
  exact f g hfg F exhaustive (fun b hb _ => by
    have : b = 0 := by simpa only [hzero, Submodule.mem_bot] using hb
    rw [this]
    exact Submodule.zero_mem _) lower

end Parafree.Homology.FilteredExactness
