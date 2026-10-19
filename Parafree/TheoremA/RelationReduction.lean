import Parafree.TheoremA.DividedFiltration
import Parafree.Lie.FreeModTwo
import Parafree.Linear.CommonPresentation
import Parafree.Lie.IdealReduction

/-! The actual field relation ideal is the reduction of the integral relation
ideal. Surjectivity is proved from its defining relators; the kernel uses the
already proved saturation of the integral filtration. -/

noncomputable section
namespace Parafree.TheoremA.Auxiliary

open Parafree.Lie Parafree.Linear

abbrev ambientReduction : Free ℤ →ₗ⁅ℤ⁆ Free (ZMod 2) :=
  FreeScalarExtension.generatorMap (ZMod 2) (Fin 3)

@[simp] theorem ambientReduction_generator (i : Fin 3) :
    ambientReduction (generator ℤ i) = generator (ZMod 2) i :=
  FreeScalarExtension.generatorMap_of (ZMod 2) (Fin 3) i

@[simp] theorem ambientReduction_relator (i : Fin 3) :
    ambientReduction (relator ℤ i) = relator (ZMod 2) i := by
  fin_cases i <;> simp [relator, map_sub, map_add, LieHom.map_lie, ambientReduction_generator]

theorem ambientReduction_mem_relation {x : Free ℤ} (hx : x ∈ relationIdeal ℤ) :
    ambientReduction x ∈ relationIdeal (ZMod 2) :=
  integralMap_mem_lieSpan ambientReduction (relator ℤ) (relator (ZMod 2))
    ambientReduction_relator hx

def relationReduction : relationIdeal ℤ →ₗ⁅ℤ⁆ relationIdeal (ZMod 2) where
  toFun x := ⟨ambientReduction x, ambientReduction_mem_relation x.property⟩
  map_add' x y := Subtype.ext (map_add ambientReduction (x : Free ℤ) (y : Free ℤ))
  map_smul' c x := Subtype.ext (map_smul ambientReduction c (x : Free ℤ))
  map_lie' {x y} := Subtype.ext (ambientReduction.map_lie (x : Free ℤ) (y : Free ℤ))

@[simp] theorem relationReduction_coe (x : relationIdeal ℤ) :
    (relationReduction x : Free (ZMod 2)) = ambientReduction x := rfl

/-- Lifting ideal generation uses only surjectivity of reduction of the ambient
free Lie algebra and the three specified integral relators. -/
theorem relationReduction_surjective : Function.Surjective relationReduction := by
  intro y
  obtain ⟨x, hx⟩ := integralMap_lieSpan_lift ambientReduction (relator ℤ) (relator (ZMod 2))
    ambientReduction_relator (FreeModTwo.generatorMap_surjective (Fin 3)) y.property
  exact ⟨x, Subtype.ext hx⟩

theorem relationReduction_eq_zero_iff (x : relationIdeal ℤ) :
    relationReduction x = 0 ↔ ∃ y : relationIdeal ℤ, (2 : ℤ) • y = x := by
  constructor
  · intro hx
    have ha : ambientReduction (x : Free ℤ) = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (FreeModTwo.generatorMap_eq_zero_iff (Fin 3) x).mp ha
    have htwo : (2 : ℤ) • y ∈ dividedFiltration 1 := by
      rw [hy]
      exact (mem_dividedFiltration_succ 0 x).mpr ⟨x.property, LieSubmodule.mem_top _⟩
    have hyF := dividedFiltration_saturated 2 (by decide) 1 y htwo
    obtain ⟨hyJ, _⟩ := (mem_dividedFiltration_succ 0 y).mp hyF
    exact ⟨⟨y, hyJ⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change ambientReduction ((2 : ℤ) • (y : Free ℤ)) = 0
    exact (FreeModTwo.generatorMap_eq_zero_iff (Fin 3) _).mpr ⟨y, rfl⟩

theorem relationReduction_ker :
    LinearMap.ker relationReduction.toLinearMap = ModScalar.multiples (2 : ℤ) (relationIdeal ℤ) := by
  ext x
  exact relationReduction_eq_zero_iff x

/-- The actual relation ideal over the field, with a formula on every integral representative. -/
def relationReductionEquiv : ModScalar.Quotient (2 : ℤ) (relationIdeal ℤ) ≃ₗ[ℤ]
    relationIdeal (ZMod 2) :=
  equivOfCommonPresentation (ModScalar.mk (2 : ℤ) (relationIdeal ℤ)) relationReduction.toLinearMap
    (ModScalar.mk_surjective (2 : ℤ) _) relationReduction_surjective (by
      rw [relationReduction_ker]
      exact Submodule.ker_mkQ _)

theorem relationReductionEquiv_mk (x : relationIdeal ℤ) :
    relationReductionEquiv (ModScalar.mk (2 : ℤ) _ x) = relationReduction x :=
  equivOfCommonPresentation_apply _ _ _ _ _ x

end Parafree.TheoremA.Auxiliary
