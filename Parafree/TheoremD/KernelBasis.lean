import Parafree.TheoremD.NormalFiltration

/-! Exact description of every kernel power in the normal-word basis. -/
noncomputable section
namespace Parafree.TheoremD.KernelBasis
open Parafree.TheoremC
open Parafree.Associative NormalWords NormalRepresentation NormalBasis NormalFiltration
variable (k : Type*) [CommRing k]

theorem wordValue_mem_kernel_power (w : Word) : wordValue k w ∈ kernel k ^ countZ w := by
  induction w with
  | nil => rw [wordValue_nil]; simp [countZ, Submodule.pow_zero, Ideal.one_eq_top]
  | cons i w ih =>
    rw [wordValue_cons]
    cases i with
    | inl i =>
      rw [countZ_Y]
      exact (kernel k ^ countZ w).mul_mem_left _ ih
    | inr n =>
      rw [countZ_Z, Ideal.IsTwoSided.pow_succ]
      exact Ideal.mul_mem_mul (show value k (Z n) ∈ kernel k from full_relator k (n+2)) ih

theorem ideal_le_kernel_power (h : ℕ) : ideal k h ≤ kernel k ^ h := by
  intro a ha
  have hgen : ∀ v ∈ level k h, evaluate k v ∈ kernel k ^ h := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w,hw,rfl⟩ := hv
      rw [evaluate_basis]
      have hle : kernel k ^ countZ w.val ≤ kernel k ^ h := Ideal.pow_le_pow_right hw
      exact hle (wordValue_mem_kernel_power k w.val)
    | zero => simp
    | add x y _ _ hx hy => simpa using (kernel k ^ h).add_mem hx hy
    | smul c x _ hx => simpa using ((kernel k ^ h).restrictScalars k).smul_mem c hx
  have he : evaluate k (represent k a) = a := LinearMap.congr_fun (evaluate_represent k) a
  simpa only [he] using hgen (represent k a) ha

theorem relator_mem_ideal_one (n : ℕ) : toInitial k (relator k n) ∈ ideal k 1 := by
  cases n with
  | zero =>
    rw [show toInitial k (relator k 0) = 0 from initial_relator k (0 : Fin 2)]
    exact (ideal k 1).zero_mem
  | succ n =>
    cases n with
    | zero =>
      rw [show toInitial k (relator k 1) = 0 from initial_relator k (1 : Fin 2)]
      exact (ideal k 1).zero_mem
    | succ n =>
      have hw : Normal [Z n] := normal_prepend (by simp) normal_nil
      have he : represent k (toInitial k (relator k (n+2))) = basis k ⟨[Z n],hw⟩ := by
        simpa [wordValue, value] using represent_wordValue k [Z n] hw
      change represent k (toInitial k (relator k (n+2))) ∈ level k 1
      rw [he]
      exact basis_mem k 1 _ (by simp [countZ])

theorem kernel_le_ideal_one : kernel k ≤ ideal k 1 := by
  intro x hx
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective k (initialIdeal k) x
  have ha : a ∈ fullIdeal k := Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hle : fullIdeal k ≤ RingHom.ker
      ((Ideal.Quotient.mkₐ k (ideal k 1)).comp (toInitial k)) := by
    apply twoSidedSpan_le
    rintro _ ⟨n,rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (relator_mem_ideal_one k n)
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hle ha)

theorem kernel_power_le_ideal (h : ℕ) : kernel k ^ h ≤ ideal k h := by
  induction h with
  | zero =>
    intro a _
    change represent k a ∈ level k 0
    rw [level_zero]
    trivial
  | succ h ih =>
    rw [Submodule.pow_succ]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    exact mul_mem_level k (ih ha) (kernel_le_ideal_one k hb)

/-- The h-th kernel power consists exactly of the linear combinations of
normal words containing at least h auxiliary relator letters. -/
theorem ideal_eq_kernel_power (h : ℕ) : ideal k h = kernel k ^ h :=
  le_antisymm (ideal_le_kernel_power k h) (kernel_power_le_ideal k h)

theorem mem_kernel_power_iff (h : ℕ) (a : A₀ k) :
    a ∈ kernel k ^ h ↔ represent k a ∈ level k h := by
  rw [← ideal_eq_kernel_power]
  rfl

end Parafree.TheoremD.KernelBasis
