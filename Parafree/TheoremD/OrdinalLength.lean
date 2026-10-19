import Parafree.TheoremD.OrdinalLowerBound
import Parafree.TheoremD.LayerMultiplication
import Parafree.TheoremD.KernelSeparation

/-! The exact transfinite stabilization length of the actual augmentation ideal. -/
noncomputable section
namespace Parafree.TheoremD
open Parafree.TheoremC
open Parafree.Associative LayerEmbedding
variable (k : Type*) [CommRing k]

private abbrev targetIdeal := augmentationIdeal (FreeAlgebra.algebraMapInv : Target k →ₐ[k] k)

theorem layer_mem_finite_tail (α : Ordinal) (h : ℕ)
    (hbase : ordinalPower k α ≤ kernel k ^ h) (n : ℕ) {x : A₀ k}
    (hx : x ∈ ordinalPower k (α+n)) : layer k h x ∈ targetIdeal k ^ n := by
  induction n generalizing x with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial
  | succ n ih =>
    have hmon : ordinalPower k (α+n) ≤ kernel k ^ h :=
      (ordinalPower_antitone k le_self_add).trans hbase
    have hl : ∀ z ∈ ordinalPower k (α+n) * initialAugmentationIdeal k,
        layer k h z ∈ targetIdeal k ^ (n+1) := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        have he := layer_mul k (m := h) (n := 0) (hmon ha) (mem_kernel_pow_zero k b)
        simp only [Nat.add_zero] at he
        rw [he, Submodule.pow_succ]
        exact Ideal.mul_mem_mul (ih ha) (layer_zero_mem_augmentation k hb)
      · intro a b ha hb
        simpa only [map_add] using (targetIdeal k ^ (n+1)).add_mem ha hb
    have hr : ∀ z ∈ initialAugmentationIdeal k * ordinalPower k (α+n),
        layer k h z ∈ targetIdeal k ^ (n+1) := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        have he := layer_mul k (m := 0) (n := h) (mem_kernel_pow_zero k a) (hmon hb)
        simp only [Nat.zero_add] at he
        rw [he, Ideal.IsTwoSided.pow_succ]
        exact Ideal.mul_mem_mul (layer_zero_mem_augmentation k ha) (ih hb)
      · intro a b ha hb
        simpa only [map_add] using (targetIdeal k ^ (n+1)).add_mem ha hb
    rw [Nat.cast_succ, ← add_assoc, ordinalPower_succ] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    simpa only [map_add] using (targetIdeal k ^ (n+1)).add_mem (hl a ha) (hr b hb)

/-- Every omega-multiple stage equals the corresponding ordinary kernel power. -/
theorem ordinalPower_omega_mul (h : ℕ) : ordinalPower k (Ordinal.omega0 * h) = kernel k ^ h := by
  induction h with
  | zero => simp only [Nat.cast_zero, mul_zero, ordinalPower_zero, Submodule.pow_zero, Ideal.one_eq_top]
  | succ h ih =>
    apply le_antisymm _ (kernel_pow_le_ordinalPower_omega_mul k (h+1))
    rw [Nat.cast_succ, mul_add, mul_one, ordinalPower_add_omega]
    intro x hx
    have hx' (n : ℕ) : x ∈ ordinalPower k (Ordinal.omega0 * h+n) :=
      (Submodule.mem_iInf (fun n : ℕ => ordinalPower k (Ordinal.omega0 * h+n))).mp hx n
    have hk : x ∈ kernel k ^ h := by
      simpa only [Nat.cast_zero, add_zero, ih] using hx' 0
    have hz : layer k h x ∈ augmentationResidual
        (FreeAlgebra.algebraMapInv : Target k →ₐ[k] k) := by
      change layer k h x ∈ ⨅ n : ℕ, targetIdeal k ^ n
      exact (Submodule.mem_iInf _).mpr (fun n =>
        layer_mem_finite_tail k (Ordinal.omega0 * h) h (le_of_eq ih) n (hx' n))
    rw [FreeAugmentation.residual_eq_bot k NormalWords.TargetLetter] at hz
    exact (layer_zero_iff k h hk).mp hz

theorem ordinalPower_omega_sq_eq_iInf :
    ordinalPower k (Ordinal.omega0 * Ordinal.omega0) = ⨅ n : ℕ, kernel k ^ n := by
  have he := TransfinitePowers.power_limit_cofinal (initialAugmentationIdeal k).toTwoSided
    (Ordinal.omega0 * Ordinal.omega0)
    (Ordinal.isSuccLimit_mul_right Ordinal.omega0_pos Ordinal.isSuccLimit_omega0)
    (fun n : ℕ => Ordinal.omega0 * n)
    (fun n => (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono (Ordinal.natCast_lt_omega0 n))
    (by
      intro β hβ
      obtain ⟨γ,hγ,hβγ⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mp hβ
      obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp hγ
      exact ⟨n,hβγ.le⟩)
  change (TransfinitePowers.power (initialAugmentationIdeal k).toTwoSided _).asIdeal = _
  rw [he]
  ext x
  simp only [TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_iInf, Submodule.mem_iInf]
  apply forall_congr'
  intro n
  change x ∈ ordinalPower k (Ordinal.omega0 * n) ↔ x ∈ kernel k ^ n
  rw [ordinalPower_omega_mul]

theorem ordinalPower_omega_sq_eq_bot : ordinalPower k (Ordinal.omega0 * Ordinal.omega0) = ⊥ := by
  rw [ordinalPower_omega_sq_eq_iInf, KernelSeparation.kernel_iInf_pow_eq_bot]

theorem ordinalPower_stable_after (α : Ordinal)
    (hα : ordinalPower k α = ordinalPower k (α+1)) (β : Ordinal) (hαβ : α ≤ β) :
    ordinalPower k β = ordinalPower k α := by
  have he : TransfinitePowers.power (initialAugmentationIdeal k).toTwoSided (α+1) =
      TransfinitePowers.power (initialAugmentationIdeal k).toTwoSided α := by
    apply SetLike.ext
    intro x
    change x ∈ ordinalPower k (α+1) ↔ x ∈ ordinalPower k α
    rw [hα]
  exact congrArg TwoSidedIdeal.asIdeal
    (TransfinitePowers.stable_after (initialAugmentationIdeal k).toTwoSided α he β hαβ)

/-- Theorem D: equality at omega squared, and no equality at any earlier successor. -/
theorem augmentation_length_omega_sq [Nontrivial k] :
    ordinalPower k (Ordinal.omega0 * Ordinal.omega0) =
      ordinalPower k (Ordinal.omega0 * Ordinal.omega0 + 1) ∧
    ∀ α < Ordinal.omega0 * Ordinal.omega0, ordinalPower k α ≠ ordinalPower k (α+1) := by
  constructor
  · simp [ordinalPower_succ, ordinalPower_omega_sq_eq_bot]
  · intro α hα he
    have hs := ordinalPower_stable_after k α he _ hα.le
    rw [ordinalPower_omega_sq_eq_bot] at hs
    exact ordinalPower_ne_bot_below_omega_sq k α hα hs.symm

end Parafree.TheoremD
