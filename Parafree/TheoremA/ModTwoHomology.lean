import Parafree.TheoremA.Freeness
import Parafree.TheoremA.HomologyReduction
import Parafree.Linear.ModTwoTensor
import Parafree.Homology.ExteriorScalarChange
import Parafree.Homology.Congr

/-! Comparison with the actual CE homology over the two-element field. -/

noncomputable section

namespace Parafree.TheoremA

open LieRings.Homological.LieHomology
open Parafree.Linear Parafree.Homology
open scoped TensorProduct Parafree.Linear.ExteriorBaseChange

abbrev LmodTwo := ZMod 2 ⊗[ℤ] L

def reducedExteriorEquiv (n : ℕ) :
    ModScalar.Quotient (2 : ℤ) (⋀[ℤ]^n L) ≃ₗ[ℤ] (⋀[ZMod 2]^n LmodTwo) :=
  (ModScalar.tensorTwoEquiv (⋀[ℤ]^n L)).symm.trans
    ((ExteriorBaseChange.freeEquiv (M := L) (ZMod 2) n).restrictScalars ℤ)

@[simp] theorem reducedExteriorEquiv_mk (n : ℕ) (x : ⋀[ℤ]^n L) :
    reducedExteriorEquiv n (ModScalar.mk (2 : ℤ) (⋀[ℤ]^n L) x) =
      ExteriorBaseChange.inclusion (ZMod 2) n x := by
  simp only [reducedExteriorEquiv, LinearEquiv.trans_apply,
    ModScalar.tensorTwoEquiv_symm_mk]
  exact ExteriorBaseChange.freeEquiv_one_tmul (ZMod 2) n x

def modTwoDifferential (n : ℕ) :
    (⋀[ZMod 2]^(n + 1) LmodTwo) →ₗ[ℤ] (⋀[ZMod 2]^n LmodTwo) :=
  (differential (ZMod 2) LmodTwo n).restrictScalars ℤ

theorem modTwoDifferential_comp : (modTwoDifferential 1).comp (modTwoDifferential 2) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (differential_comp_differential (ZMod 2) LmodTwo 1) x

theorem reducedExteriorEquiv_differential_one
    (x : ModScalar.Quotient (2 : ℤ) (⋀[ℤ]^2 L)) :
    reducedExteriorEquiv 1 (ModScalar.map (2 : ℤ) (differential ℤ L 1) x) =
      modTwoDifferential 1 (reducedExteriorEquiv 2 x) := by
  obtain ⟨x, rfl⟩ := ModScalar.mk_surjective (2 : ℤ) (⋀[ℤ]^2 L) x
  change reducedExteriorEquiv 1
    (ModScalar.mk (2 : ℤ) (⋀[ℤ]^1 L) (differential ℤ L 1 x)) = _
  rw [reducedExteriorEquiv_mk, reducedExteriorEquiv_mk]
  exact ExteriorScalarChange.inclusion_differential_one (ZMod 2) x

theorem reducedExteriorEquiv_differential_two
    (x : ModScalar.Quotient (2 : ℤ) (⋀[ℤ]^3 L)) :
    reducedExteriorEquiv 2 (ModScalar.map (2 : ℤ) (differential ℤ L 2) x) =
      modTwoDifferential 2 (reducedExteriorEquiv 3 x) := by
  obtain ⟨x, rfl⟩ := ModScalar.mk_surjective (2 : ℤ) (⋀[ℤ]^3 L) x
  change reducedExteriorEquiv 2
    (ModScalar.mk (2 : ℤ) (⋀[ℤ]^2 L) (differential ℤ L 2 x)) = _
  rw [reducedExteriorEquiv_mk, reducedExteriorEquiv_mk]
  exact ExteriorScalarChange.inclusion_differential_two (ZMod 2) x

def reducedCEHomologyTwoEquiv : ReducedCEHomologyTwo ≃+ SecondHomology (ZMod 2) LmodTwo :=
  ScalarReduction.congrAddEquiv _ _ _ _ _ modTwoDifferential_comp
    (reducedExteriorEquiv 1) (reducedExteriorEquiv 2) (reducedExteriorEquiv 3)
    reducedExteriorEquiv_differential_one reducedExteriorEquiv_differential_two

/-- The genuine CE universal-coefficient isomorphism, including exterior scalar change. -/
def homologyTwoModTwoEquiv :
    ModScalar.Quotient (2 : ℤ) (Homology (R := ℤ) (L := L) 2) ≃ₗ[ℤ]
      Homology (R := ZMod 2) (L := LmodTwo) 2 :=
  ((homologyTwoReductionEquiv.toAddEquiv.trans reducedCEHomologyTwoEquiv).trans
    (secondHomologyConcreteIso (ZMod 2) LmodTwo).toLinearEquiv.symm.toAddEquiv).toIntLinearEquiv

/-- Universal coefficients as a linear equivalence over the two-element field. -/
def homologyTwoTensorModTwoEquiv :
    (ZMod 2 ⊗[ℤ] Homology (R := ℤ) (L := L) 2) ≃ₗ[ZMod 2]
      Homology (R := ZMod 2) (L := LmodTwo) 2 := by
  let e := (ModScalar.tensorTwoAddEquiv (Homology (R := ℤ) (L := L) 2)).trans
    homologyTwoModTwoEquiv.toAddEquiv
  exact { e with map_smul' := ZMod.map_smul e }

end Parafree.TheoremA
