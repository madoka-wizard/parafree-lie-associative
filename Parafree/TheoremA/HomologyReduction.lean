import Parafree.TheoremA.Reduction
import Parafree.Homology.ScalarReduction
import LieRings.Homological.LieHomology.DegreeTwo

/-!
Reduction of the actual second CE homology modulo two. The target here is the
homology of the degreewise reduced integral CE complex. Identifying that complex
with the CE complex of the Lie algebra after scalar change is a separate step.
-/

noncomputable section

namespace Parafree.TheoremA

open LieRings.Homological.LieHomology
open Parafree.Linear Parafree.Homology

theorem differential_one_two_saturated (y : ⋀[ℤ]^1 L)
    (hy : (2 : ℤ) • y ∈ (differential ℤ L 1).range) :
    y ∈ (differential ℤ L 1).range := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨t, ht⟩ := degreeTwoBoundary_two_saturated (y := exteriorPower.oneEquiv ℤ L y) (by
    refine ⟨z, ?_⟩
    change exteriorPower.oneEquiv ℤ L (differential ℤ L 1 z) = _
    rw [hz, map_smul])
  refine ⟨t, (exteriorPower.oneEquiv ℤ L).injective ?_⟩
  exact ht

theorem exterior_one_two_injective :
    Function.Injective (fun x : ⋀[ℤ]^1 L => (2 : ℤ) • x) := by
  intro x y h
  apply (exteriorPower.oneEquiv ℤ L).injective
  apply (smul_right_injective (M := L) (by decide : (2 : ℤ) ≠ 0))
  simpa only [map_smul] using congrArg (exteriorPower.oneEquiv ℤ L) h

/-- Degree-two homology of the integral CE complex reduced degreewise modulo two. -/
abbrev ReducedCEHomologyTwo :=
  ScalarReduction.ReducedHomology (differential ℤ L 1) (differential ℤ L 2)
    (differential_comp_differential ℤ L 1) (2 : ℤ)

/-- The universal-coefficient comparison, in the concrete cycles/quotient model. -/
def secondHomologyReductionEquiv :
    ModScalar.Quotient (2 : ℤ) (SecondHomology ℤ L) ≃ₗ[ℤ] ReducedCEHomologyTwo :=
  ScalarReduction.equivalence _ _ _ (2 : ℤ)
    exterior_one_two_injective differential_one_two_saturated

/-- The comparison with the upstream all-degree CE homology object. -/
def homologyTwoReductionEquiv :
    ModScalar.Quotient (2 : ℤ) (Homology (R := ℤ) (L := L) 2) ≃ₗ[ℤ]
      ReducedCEHomologyTwo := by
  let e : Homology (R := ℤ) (L := L) 2 ≃ₗ[ℤ] SecondHomology ℤ L :=
    (secondHomologyConcreteIso ℤ L).toLinearEquiv.toAddEquiv.toIntLinearEquiv
  let f : ModScalar.Quotient (2 : ℤ) (Homology (R := ℤ) (L := L) 2) ≃+
      ModScalar.Quotient (2 : ℤ) (SecondHomology ℤ L) := ModScalar.congrAdd 2 e
  exact (f.trans secondHomologyReductionEquiv.toAddEquiv).toIntLinearEquiv

end Parafree.TheoremA
