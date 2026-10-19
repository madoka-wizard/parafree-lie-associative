import Parafree.Lie.LowerCentral
import Parafree.Lie.ScalarExtension
import Parafree.Linear.ModNatTensor
import Parafree.Homology.ExteriorScalarChange
import Parafree.Homology.Congr
import LieRings.Homological.LieHomology.LowDegreeHomology
import LieRings.Homological.LieHomology.DegreeTwo

/-! Universal coefficients in degree two over an arbitrary nonzero modulus.
The Lie ring must be free as an integral module, and its abelianization must
be torsion-free. Both the source and target use actual CE homology. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Parafree.Homology.ModNat

open Parafree.Lie Parafree.Linear
open LieRings.Homological.LieHomology
open scoped TensorProduct Parafree.Linear.ExteriorBaseChange

variable (L : Type*) [LieRing L] [Module.Free ℤ L]
  [Module.IsTorsionFree ℤ (L ⧸ lowerCentral ℤ L 1)]
variable (p : ℕ) [NeZero p]

private theorem modulus_ne_zero : (p : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne p

omit [Module.Free ℤ L] in
private theorem degreeTwoBoundary_saturated {y : L}
    (hy : (p : ℤ) • y ∈ (degreeTwoBoundary ℤ L).range) :
    y ∈ (degreeTwoBoundary ℤ L).range := by
  have hm : (p : ℤ) • y ∈ lowerCentral ℤ L 1 := by
    rw [range_degreeTwoBoundary] at hy
    simpa only [lowerCentral, LieModule.lowerCentralSeries_succ,
      LieModule.lowerCentralSeries_zero] using hy
  have hzero : (p : ℤ) • quotientMk (lowerCentral ℤ L 1) y = 0 := by
    rw [← map_smul, quotientMk_eq_zero]
    exact hm
  have hz : quotientMk (lowerCentral ℤ L 1) y = 0 :=
    (smul_eq_zero_iff_right (modulus_ne_zero p)).mp hzero
  rw [range_degreeTwoBoundary]
  simpa only [lowerCentral, LieModule.lowerCentralSeries_succ,
    LieModule.lowerCentralSeries_zero] using (quotientMk_eq_zero _ y).mp hz

omit [Module.Free ℤ L] in
private theorem differential_one_saturated (y : ⋀[ℤ]^1 L)
    (hy : (p : ℤ) • y ∈ (differential ℤ L 1).range) :
    y ∈ (differential ℤ L 1).range := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨b, hb⟩ := degreeTwoBoundary_saturated L p (y := exteriorPower.oneEquiv ℤ L y) (by
    refine ⟨z, ?_⟩
    change exteriorPower.oneEquiv ℤ L (differential ℤ L 1 z) = _
    rw [hz, map_smul])
  exact ⟨b, (exteriorPower.oneEquiv ℤ L).injective hb⟩

omit [Module.IsTorsionFree ℤ (L ⧸ lowerCentral ℤ L 1)] in
private theorem exterior_one_injective :
    Function.Injective (fun z : ⋀[ℤ]^1 L => (p : ℤ) • z) := by
  intro z w he
  apply (exteriorPower.oneEquiv ℤ L).injective
  apply smul_right_injective (M := L) (modulus_ne_zero p)
  simpa only [map_smul] using congrArg (exteriorPower.oneEquiv ℤ L) he

abbrev ReducedCEHomologyTwo :=
  ScalarReduction.ReducedHomology (differential ℤ L 1) (differential ℤ L 2)
    (differential_comp_differential ℤ L 1) (p : ℤ)

def secondHomologyReductionEquiv :
    ModScalar.Quotient (p : ℤ) (SecondHomology ℤ L) ≃ₗ[ℤ] ReducedCEHomologyTwo L p :=
  ScalarReduction.equivalence _ _ _ (p : ℤ)
    (exterior_one_injective L p) (differential_one_saturated L p)

def homologyTwoReductionEquiv :
    ModScalar.Quotient (p : ℤ) (Homology (R := ℤ) (L := L) 2) ≃ₗ[ℤ]
      ReducedCEHomologyTwo L p := by
  let e : Homology (R := ℤ) (L := L) 2 ≃ₗ[ℤ] SecondHomology ℤ L :=
    (secondHomologyConcreteIso ℤ L).toLinearEquiv.toAddEquiv.toIntLinearEquiv
  exact ((ModScalar.congrAdd (p : ℤ) e).trans
    (secondHomologyReductionEquiv L p).toAddEquiv).toIntLinearEquiv

abbrev Reduced := ZMod p ⊗[ℤ] L

def reducedExteriorEquiv (n : ℕ) :
    ModScalar.Quotient (p : ℤ) (⋀[ℤ]^n L) ≃ₗ[ℤ] (⋀[ZMod p]^n (Reduced L p)) :=
  (ModScalar.tensorNatEquiv p (⋀[ℤ]^n L)).symm.trans
    ((ExteriorBaseChange.freeEquiv (M := L) (ZMod p) n).restrictScalars ℤ)

omit [Module.IsTorsionFree ℤ (L ⧸ lowerCentral ℤ L 1)] [NeZero p] in
@[simp] theorem reducedExteriorEquiv_mk (n : ℕ) (z : ⋀[ℤ]^n L) :
    reducedExteriorEquiv L p n (ModScalar.mk (p : ℤ) (⋀[ℤ]^n L) z) =
      ExteriorBaseChange.inclusion (ZMod p) n z := by
  simp only [reducedExteriorEquiv, LinearEquiv.trans_apply,
    ModScalar.tensorNatEquiv_symm_mk]
  exact ExteriorBaseChange.freeEquiv_one_tmul (ZMod p) n z

def reducedDifferential (n : ℕ) :
    (⋀[ZMod p]^(n + 1) (Reduced L p)) →ₗ[ℤ] (⋀[ZMod p]^n (Reduced L p)) :=
  (differential (ZMod p) (Reduced L p) n).restrictScalars ℤ

omit [Module.Free ℤ L] [Module.IsTorsionFree ℤ (L ⧸ lowerCentral ℤ L 1)] [NeZero p] in
theorem reducedDifferential_comp :
    (reducedDifferential L p 1).comp (reducedDifferential L p 2) = 0 := by
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun (differential_comp_differential (ZMod p) (Reduced L p) 1) z

omit [Module.IsTorsionFree ℤ (L ⧸ lowerCentral ℤ L 1)] [NeZero p] in
theorem reducedExteriorEquiv_differential_one
    (z : ModScalar.Quotient (p : ℤ) (⋀[ℤ]^2 L)) :
    reducedExteriorEquiv L p 1 (ModScalar.map (p : ℤ) (differential ℤ L 1) z) =
      reducedDifferential L p 1 (reducedExteriorEquiv L p 2 z) := by
  obtain ⟨z, rfl⟩ := ModScalar.mk_surjective (p : ℤ) (⋀[ℤ]^2 L) z
  change reducedExteriorEquiv L p 1
    (ModScalar.mk (p : ℤ) (⋀[ℤ]^1 L) (differential ℤ L 1 z)) = _
  rw [reducedExteriorEquiv_mk, reducedExteriorEquiv_mk]
  exact ExteriorScalarChange.inclusion_differential_one (ZMod p) z

omit [Module.IsTorsionFree ℤ (L ⧸ lowerCentral ℤ L 1)] [NeZero p] in
theorem reducedExteriorEquiv_differential_two
    (z : ModScalar.Quotient (p : ℤ) (⋀[ℤ]^3 L)) :
    reducedExteriorEquiv L p 2 (ModScalar.map (p : ℤ) (differential ℤ L 2) z) =
      reducedDifferential L p 2 (reducedExteriorEquiv L p 3 z) := by
  obtain ⟨z, rfl⟩ := ModScalar.mk_surjective (p : ℤ) (⋀[ℤ]^3 L) z
  change reducedExteriorEquiv L p 2
    (ModScalar.mk (p : ℤ) (⋀[ℤ]^2 L) (differential ℤ L 2 z)) = _
  rw [reducedExteriorEquiv_mk, reducedExteriorEquiv_mk]
  exact ExteriorScalarChange.inclusion_differential_two (ZMod p) z

def reducedCEHomologyTwoEquiv :
    ReducedCEHomologyTwo L p ≃+ SecondHomology (ZMod p) (Reduced L p) :=
  ScalarReduction.congrAddEquiv _ _ _ _ _ (reducedDifferential_comp L p)
    (reducedExteriorEquiv L p 1) (reducedExteriorEquiv L p 2) (reducedExteriorEquiv L p 3)
    (reducedExteriorEquiv_differential_one L p) (reducedExteriorEquiv_differential_two L p)

def homologyTwoModEquiv :
    ModScalar.Quotient (p : ℤ) (Homology (R := ℤ) (L := L) 2) ≃ₗ[ℤ]
      Homology (R := ZMod p) (L := Reduced L p) 2 :=
  (((homologyTwoReductionEquiv L p).toAddEquiv.trans (reducedCEHomologyTwoEquiv L p)).trans
    (secondHomologyConcreteIso (ZMod p) (Reduced L p)).toLinearEquiv.symm.toAddEquiv).toIntLinearEquiv

/-- The actual universal-coefficient isomorphism over `ZMod p`. -/
def homologyTwoTensorEquiv :
    (ZMod p ⊗[ℤ] Homology (R := ℤ) (L := L) 2) ≃ₗ[ZMod p]
      Homology (R := ZMod p) (L := Reduced L p) 2 := by
  let e := (ModScalar.tensorNatAddEquiv p (Homology (R := ℤ) (L := L) 2)).trans
    (homologyTwoModEquiv L p).toAddEquiv
  exact { e with map_smul' := ZMod.map_smul e }

end Parafree.Homology.ModNat
