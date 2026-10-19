import Parafree.TheoremA.ScalarModel

/-! The residual ideal of the presentation is exactly its two-primary additive torsion. -/

noncomputable section

namespace Parafree.TheoremA

open Parafree.Lie
open scoped TensorProduct

abbrev InvertTwo := Localization (Submonoid.powers (2 : ℤ))

/-- Use the canonical integer algebra consistently with Lie scalar extension. -/
theorem invertTwoIsLocalization :
    @IsLocalization ℤ _ (Submonoid.powers (2 : ℤ)) InvertTwo _
      (Ring.toIntAlgebra InvertTwo) := by
  have he : Ring.toIntAlgebra InvertTwo = (inferInstance : Algebra ℤ InvertTwo) :=
    Subsingleton.elim _ _
  rw [he]
  infer_instance

local instance : Algebra ℤ InvertTwo := Ring.toIntAlgebra InvertTwo
attribute [local instance] invertTwoIsLocalization

namespace K

private def half : InvertTwo := IsLocalization.Away.invSelf (2 : ℤ)

private theorem two_mul_half : (2 : InvertTwo) * half = 1 := by
  simpa using IsLocalization.Away.mul_invSelf (S := InvertTwo) (2 : ℤ)

private theorem localized_two_injective :
    Function.Injective (fun x : InvertTwo ⊗[ℤ] K => (2 : ℤ) • x) :=
  ScalarExtension.int_two_smul_injective InvertTwo half two_mul_half _

private def inverseEvaluation : FreeThree →ₗ⁅ℤ⁆ InvertTwo ⊗[ℤ] K :=
  FreeLieAlgebra.lift ℤ (fun i => half • ((1 : InvertTwo) ⊗ₜ[ℤ] x i))

private theorem inverseEvaluation_comp :
    inverseEvaluation.comp integralEvaluation =
      Parafree.Homology.ExteriorScalarChange.tensorUnit InvertTwo := by
  apply hom_ext_of_two_smul_injective localized_two_injective
  intro i
  change inverseEvaluation (integralEvaluation (x i)) = (1 : InvertTwo) ⊗ₜ[ℤ] x i
  rw [integralEvaluation_x, integralX, map_smul]
  rw [show inverseEvaluation (FreeLieAlgebra.of ℤ i) =
    half • ((1 : InvertTwo) ⊗ₜ[ℤ] x i) from FreeLieAlgebra.lift_of_apply _ _]
  exact ScalarExtension.int_two_smul_half InvertTwo half two_mul_half _

theorem two_primary_of_mem_residual {a : K} (ha : a ∈ residualIdeal ℤ K) :
    ∃ n : ℕ, (2 ^ n : ℤ) • a = 0 := by
  have he : integralEvaluation a = 0 := by
    change a ∈ integralEvaluation.ker
    rwa [integralEvaluation_ker]
  have ht : (1 : InvertTwo) ⊗ₜ[ℤ] a = 0 := by
    have h := DFunLike.congr_fun inverseEvaluation_comp a
    change inverseEvaluation (integralEvaluation a) = _ at h
    rw [he, map_zero] at h
    exact h.symm
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (2 : ℤ))
    (TensorProduct.mk ℤ InvertTwo K 1)).mp ht
  obtain ⟨n, hn⟩ := s.property
  refine ⟨n, ?_⟩
  change (s : ℤ) • a = 0 at hs
  simpa only [← hn] using hs

/-- This characterizes the exact residual ideal, rather than only an ideal contained in it. -/
theorem mem_residual_iff_two_primary (a : K) :
    a ∈ residualIdeal ℤ K ↔ ∃ n : ℕ, (2 ^ n : ℤ) • a = 0 := by
  refine ⟨two_primary_of_mem_residual, ?_⟩
  rintro ⟨n, hn⟩
  apply (quotientMk_eq_zero (residualIdeal ℤ K) a).mp
  change toL a = 0
  apply (smul_eq_zero_iff_right (pow_ne_zero n (by decide : (2 : ℤ) ≠ 0))).mp
  rw [← map_smul, hn, map_zero]

variable {M : Type*} [LieRing M]

theorem residual_le_ker (f : K →ₗ⁅ℤ⁆ M)
    (h₂ : Function.Injective (fun x : M => (2 : ℤ) • x)) :
    residualIdeal ℤ K ≤ f.ker := by
  intro a ha
  obtain ⟨n, hn⟩ := two_primary_of_mem_residual ha
  have h : (2 ^ n : ℤ) • f a = 0 := by rw [← map_smul, hn, map_zero]
  clear hn
  change f a = 0
  induction n with
  | zero => simpa only [pow_zero, one_smul] using h
  | succ n ih =>
    apply ih
    apply h₂
    change (2 : ℤ) • ((2 ^ n : ℤ) • f a) = (2 : ℤ) • (0 : M)
    rw [smul_zero, ← mul_smul, ← pow_succ']
    exact h

/-- Every map from the presentation to a Lie ring without additive two-torsion descends. -/
def descend (f : K →ₗ⁅ℤ⁆ M)
    (h₂ : Function.Injective (fun x : M => (2 : ℤ) • x)) : L →ₗ⁅ℤ⁆ M :=
  quotientLift (residualIdeal ℤ K) f (residual_le_ker f h₂)

@[simp] theorem descend_toL (f : K →ₗ⁅ℤ⁆ M)
    (h₂ : Function.Injective (fun x : M => (2 : ℤ) • x)) (a : K) :
    descend f h₂ (toL a) = f a := rfl

end K
end Parafree.TheoremA
