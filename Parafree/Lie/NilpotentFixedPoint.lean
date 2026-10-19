import Parafree.Lie.LowerCentral

/-! Finite iteration solves filtration-contracting equations in nilpotent Lie algebras. -/

namespace Parafree.Lie

variable (R : Type*) [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L] {ι : Type*}

def FiltrationContracting (F : (ι → L) → (ι → L)) : Prop :=
  ∀ n x y, (∀ i, x i - y i ∈ lowerCentral R L n) →
    ∀ i, F x i - F y i ∈ lowerCentral R L (n + 1)

variable {R}

theorem fixedPoint_unique {F : (ι → L) → (ι → L)} (hF : FiltrationContracting R F)
    (n : ℕ) (hn : lowerCentral R L n = ⊥) {x y : ι → L}
    (hx : F x = x) (hy : F y = y) : x = y := by
  have hdiff (k : ℕ) : ∀ i, x i - y i ∈ lowerCentral R L k := by
    induction k with
    | zero => intro i; exact LieSubmodule.mem_top _
    | succ k ih => simpa only [hx, hy] using hF k x y ih
  funext i
  exact sub_eq_zero.mp (by simpa only [hn, LieSubmodule.mem_bot] using hdiff n i)

theorem iterate_isFixed {F : (ι → L) → (ι → L)} (hF : FiltrationContracting R F)
    (n : ℕ) (hn : lowerCentral R L n = ⊥) (x : ι → L) :
    F (F^[n] x) = F^[n] x := by
  have hdiff (k : ℕ) : ∀ i, F (F^[k] x) i - F^[k] x i ∈ lowerCentral R L k := by
    induction k with
    | zero => intro i; exact LieSubmodule.mem_top _
    | succ k ih =>
      simpa only [Function.iterate_succ_apply'] using hF k (F (F^[k] x)) (F^[k] x) ih
  funext i
  exact sub_eq_zero.mp (by simpa only [hn, LieSubmodule.mem_bot] using hdiff n i)

theorem existsUnique_fixedPoint {F : (ι → L) → (ι → L)}
    (hF : FiltrationContracting R F) (n : ℕ) (hn : lowerCentral R L n = ⊥) :
    ∃! x, F x = x := by
  refine ⟨F^[n] 0, iterate_isFixed hF n hn 0, ?_⟩
  intro y hy
  exact fixedPoint_unique hF n hn hy (iterate_isFixed hF n hn 0)

theorem lie_mem_lowerCentral_succ_right (n : ℕ) (x : L) {y : L}
    (hy : y ∈ lowerCentral R L n) : ⁅x, y⁆ ∈ lowerCentral R L (n + 1) := by
  simp only [lowerCentral, LieModule.lowerCentralSeries_succ]
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy

theorem lie_mem_lowerCentral_succ_left (n : ℕ) {x : L} (y : L)
    (hx : x ∈ lowerCentral R L n) : ⁅x, y⁆ ∈ lowerCentral R L (n + 1) := by
  rw [← lie_skew x y]
  exact (lowerCentral R L (n + 1)).neg_mem (lie_mem_lowerCentral_succ_right n y hx)

theorem lie_sub_lie_mem_lowerCentral_succ (n : ℕ) {a b c d : L}
    (hac : a - c ∈ lowerCentral R L n) (hbd : b - d ∈ lowerCentral R L n) :
    ⁅a, b⁆ - ⁅c, d⁆ ∈ lowerCentral R L (n + 1) := by
  have heq : ⁅a, b⁆ - ⁅c, d⁆ = ⁅a - c, b⁆ + ⁅c, b - d⁆ := by
    simp only [sub_lie, lie_sub]
    abel
  rw [heq]
  exact (lowerCentral R L (n + 1)).add_mem
    (lie_mem_lowerCentral_succ_left n b hac) (lie_mem_lowerCentral_succ_right n c hbd)

end Parafree.Lie
