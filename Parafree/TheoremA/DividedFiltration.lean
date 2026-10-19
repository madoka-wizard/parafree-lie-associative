import Parafree.TheoremA.RelationFiltration
import Parafree.Linear.DividedFiltration

/-! The integral descending relation filtration, with its proved saturation.
Together with finite denominator cancellation this supplies the injectivity
criterion for divided reduction, without choosing adapted bases. -/

noncomputable section
namespace Parafree.TheoremA.Auxiliary

open Parafree.Lie

/-- The zeroth term is the ambient free Lie ring; the positive terms are the
lower central series of the actual relation ideal, embedded in that ring. -/
def dividedFiltration : ℕ → Submodule ℤ (Free ℤ)
  | 0 => ⊤
  | n + 1 => (lowerCentral ℤ (relationIdeal ℤ) n).toSubmodule.map
      (relationIdeal ℤ).toSubmodule.subtype

@[simp] theorem dividedFiltration_zero : dividedFiltration 0 = ⊤ := rfl

@[simp] theorem mem_dividedFiltration_succ (n : ℕ) (x : Free ℤ) :
    x ∈ dividedFiltration (n + 1) ↔
      ∃ hx : x ∈ relationIdeal ℤ, (⟨x, hx⟩ : relationIdeal ℤ) ∈
        lowerCentral ℤ (relationIdeal ℤ) n := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨x, hx⟩, hy, rfl⟩

theorem dividedFiltration_antitone : Antitone dividedFiltration := by
  intro n m h
  cases n with
  | zero => exact le_top
  | succ n =>
    cases m with
    | zero => omega
    | succ m =>
      exact Submodule.map_mono (LieModule.antitone_lowerCentralSeries ℤ
        (relationIdeal ℤ) (relationIdeal ℤ) (by omega : n ≤ m))

/-- Nonzero integer division preserves each relation-filtration term. -/
theorem dividedFiltration_saturated (p : ℤ) (hp : p ≠ 0) :
    Parafree.Linear.DividedFiltration.Saturated dividedFiltration p := by
  intro n x hx
  cases n with
  | zero => exact Submodule.mem_top
  | succ n =>
    obtain ⟨hpx, hy⟩ := (mem_dividedFiltration_succ n (p • x)).mp hx
    have hxJ : x ∈ relationIdeal ℤ := by
      letI : Module.IsTorsionFree ℤ (Presented ℤ) := (presentedBasis ℤ).isTorsionFree
      apply (quotientMk_eq_zero _ _).mp
      apply (smul_eq_zero_iff_right hp).mp
      rw [← map_smul, quotientMk_eq_zero]
      exact hpx
    refine (mem_dividedFiltration_succ n x).mpr ⟨hxJ, ?_⟩
    letI : Module.Free ℤ (relationIdeal ℤ ⧸ lowerCentral ℤ (relationIdeal ℤ) n) :=
      relationIdeal_nilpotent_free n
    letI : Module.IsTorsionFree ℤ
        (relationIdeal ℤ ⧸ lowerCentral ℤ (relationIdeal ℤ) n) :=
      (Module.Free.chooseBasis ℤ _).isTorsionFree
    apply (quotientMk_eq_zero _ _).mp
    apply (smul_eq_zero_iff_right hp).mp
    rw [← map_smul, quotientMk_eq_zero]
    exact hy

/-- The finite injectivity criterion specialized to the actual relation ideal. -/
theorem dividedFiltration_term_decomposition
    (x y : ℕ → Free ℤ) (n : ℕ)
    (hx : ∀ j ≤ n, x j ∈ dividedFiltration j)
    (hy : ∀ j ≤ n, y j ∈ dividedFiltration j)
    (h : Parafree.Linear.DividedFiltration.numerator (2 : ℤ) x n =
      (2 : ℤ) • Parafree.Linear.DividedFiltration.numerator (2 : ℤ) y n)
    (j : ℕ) (hj : j ≤ n) :
    ∃ a ∈ dividedFiltration (j + 1), ∃ b ∈ dividedFiltration j,
      x j = a + (2 : ℤ) • b :=
  Parafree.Linear.DividedFiltration.term_decomposition_of_divisible
    dividedFiltration 2 dividedFiltration_antitone
    (dividedFiltration_saturated 2 (by decide)) x y n hx hy h j hj

end Parafree.TheoremA.Auxiliary
