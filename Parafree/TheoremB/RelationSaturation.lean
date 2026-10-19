import Parafree.TheoremB.AuxiliaryScalarExtension

/-! Five-saturation of the exact integral relation ideal.
Only the localized auxiliary quotient is assumed free, via its proved
presentation comparison; integral freeness of that quotient is not assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB.Auxiliary
open Parafree.Lie
open scoped TensorProduct
local instance : Algebra ℤ AtFive := Ring.toIntAlgebra AtFive
local instance : IsLocalization fiveIdeal.primeCompl AtFive := by
  have h := Localization.isLocalization (M := fiveIdeal.primeCompl)
  convert h using 1
  exact Subsingleton.elim _ _

theorem five_coprime_denominator (s : fiveIdeal.primeCompl) : IsCoprime (5:ℤ) (s:ℤ) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  change Nat.Coprime 5 (s:ℤ).natAbs
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr
  intro hs
  have hd : (5:ℤ) ∣ (s:ℤ) := Int.natCast_dvd.mpr hs
  exact s.property ((Ideal.mem_span_singleton).mpr hd)

theorem presented_five_torsion_free (z : Presented ℤ) (hz : (5:ℤ) • z = 0) : z = 0 := by
  letI : Module.IsTorsionFree AtFive (Presented AtFive) :=
    (Module.Free.chooseBasis AtFive (Presented AtFive)).isTorsionFree
  have hn : (5:AtFive) ≠ 0 := by
    intro he
    have hi := IsLocalization.injective AtFive fiveIdeal.primeCompl_le_nonZeroDivisors
    have heq : algebraMap ℤ AtFive 5 = algebraMap ℤ AtFive 0 := by simpa using he
    exact (by decide : (5:ℤ) ≠ 0) (hi heq)
  have hloc : integralMap AtFive z = 0 := by
    apply (smul_eq_zero_iff_right hn).mp
    change ((5:ℤ):AtFive) • integralMap AtFive z = 0
    rw [Int.cast_smul_eq_zsmul,← map_zsmul,hz,map_zero]
  have hu : (1:AtFive) ⊗ₜ[ℤ] z = 0 := by
    apply (scalarEquiv AtFive).injective
    change scalarForward AtFive (1 ⊗ₜ[ℤ] z) = scalarForward AtFive 0
    rw [scalarForward_one,hloc,map_zero]
  obtain ⟨s,hs⟩ := (IsLocalizedModule.eq_zero_iff fiveIdeal.primeCompl
    (TensorProduct.mk ℤ AtFive (Presented ℤ) 1)).mp hu
  change (s:ℤ) • z = 0 at hs
  obtain ⟨a,b,hab⟩ := five_coprime_denominator s
  calc
    z = (1:ℤ) • z := (one_smul ℤ z).symm
    _ = (a*5+b*(s:ℤ)) • z := by rw [hab]
    _ = 0 := by rw [add_smul,mul_smul,mul_smul,hz,hs,smul_zero,smul_zero,add_zero]

/-- Dividing an integral relation by five stays inside the same relation ideal. -/
theorem relationIdeal_five_saturated (x : Free ℤ) (hx : (5:ℤ) • x ∈ relationIdeal ℤ) :
    x ∈ relationIdeal ℤ := by
  apply (quotientMk_eq_zero _ _).mp
  apply presented_five_torsion_free
  rw [← map_zsmul,quotientMk_eq_zero]
  exact hx

end Parafree.TheoremB.Auxiliary
