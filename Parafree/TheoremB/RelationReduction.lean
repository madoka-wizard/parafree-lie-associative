import Parafree.TheoremB.RelationSaturation
import Parafree.Lie.FreeModNat
import Parafree.Linear.CommonPresentation
import Parafree.Lie.IdealReduction

/-! The actual field relation ideal is the reduction of the integral relation
ideal. Surjectivity is proved from its defining relators; the kernel uses the
already proved five-saturation of the integral ideal. -/

noncomputable section
namespace Parafree.TheoremB.Auxiliary

open Parafree.Lie Parafree.Linear

abbrev ambientReduction : Free ℤ →ₗ⁅ℤ⁆ Free (ZMod 5) :=
  FreeScalarExtension.generatorMap (ZMod 5) (Fin 2)

@[simp] theorem ambientReduction_generator (i : Fin 2) :
    ambientReduction (generator ℤ i) = generator (ZMod 5) i :=
  FreeScalarExtension.generatorMap_of (ZMod 5) (Fin 2) i

@[simp] theorem ambientReduction_relator (i : Fin 2) :
    ambientReduction (relator ℤ i) = relator (ZMod 5) i := by
  fin_cases i
  · change ambientReduction (f₁ (generator ℤ 0) (generator ℤ 1)) = f₁ (generator (ZMod 5) 0) (generator (ZMod 5) 1)
    rw [map_f₁,ambientReduction_generator,ambientReduction_generator]
  · change ambientReduction (f₂ (generator ℤ 0) (generator ℤ 1)) = f₂ (generator (ZMod 5) 0) (generator (ZMod 5) 1)
    rw [map_f₂,ambientReduction_generator,ambientReduction_generator]

theorem ambientReduction_mem_relation {x : Free ℤ} (hx : x ∈ relationIdeal ℤ) :
    ambientReduction x ∈ relationIdeal (ZMod 5) :=
  integralMap_mem_lieSpan ambientReduction (relator ℤ) (relator (ZMod 5))
    ambientReduction_relator hx

def relationReduction : relationIdeal ℤ →ₗ⁅ℤ⁆ relationIdeal (ZMod 5) where
  toFun x := ⟨ambientReduction x, ambientReduction_mem_relation x.property⟩
  map_add' x y := Subtype.ext (map_add ambientReduction (x : Free ℤ) (y : Free ℤ))
  map_smul' c x := Subtype.ext (map_smul ambientReduction c (x : Free ℤ))
  map_lie' {x y} := Subtype.ext (ambientReduction.map_lie (x : Free ℤ) (y : Free ℤ))

@[simp] theorem relationReduction_coe (x : relationIdeal ℤ) :
    (relationReduction x : Free (ZMod 5)) = ambientReduction x := rfl

/-- Lifting ideal generation uses only surjectivity of reduction of the ambient
free Lie algebra and the two specified integral relators. -/
theorem relationReduction_surjective : Function.Surjective relationReduction := by
  intro y
  obtain ⟨x, hx⟩ := integralMap_lieSpan_lift ambientReduction (relator ℤ) (relator (ZMod 5))
    ambientReduction_relator (FreeModNat.generatorMap_surjective 5 (Fin 2)) y.property
  exact ⟨x, Subtype.ext hx⟩

theorem relationReduction_eq_zero_iff (x : relationIdeal ℤ) :
    relationReduction x = 0 ↔ ∃ y : relationIdeal ℤ, (5 : ℤ) • y = x := by
  constructor
  · intro hx
    have ha : ambientReduction (x : Free ℤ) = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (FreeModNat.generatorMap_eq_zero_iff 5 (Fin 2) x).mp ha
    have hyJ : y ∈ relationIdeal ℤ := relationIdeal_five_saturated y (hy ▸ x.property)
    exact ⟨⟨y, hyJ⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change ambientReduction ((5 : ℤ) • (y : Free ℤ)) = 0
    exact (FreeModNat.generatorMap_eq_zero_iff 5 (Fin 2) _).mpr ⟨y, rfl⟩

theorem relationReduction_ker :
    LinearMap.ker relationReduction.toLinearMap = ModScalar.multiples (5 : ℤ) (relationIdeal ℤ) := by
  ext x
  exact relationReduction_eq_zero_iff x

/-- The actual relation ideal over the field, with a formula on every integral representative. -/
def relationReductionEquiv : ModScalar.Quotient (5 : ℤ) (relationIdeal ℤ) ≃ₗ[ℤ]
    relationIdeal (ZMod 5) :=
  equivOfCommonPresentation (ModScalar.mk (5 : ℤ) (relationIdeal ℤ)) relationReduction.toLinearMap
    (ModScalar.mk_surjective (5 : ℤ) _) relationReduction_surjective (by
      rw [relationReduction_ker]
      exact Submodule.ker_mkQ _)

theorem relationReductionEquiv_mk (x : relationIdeal ℤ) :
    relationReductionEquiv (ModScalar.mk (5 : ℤ) _ x) = relationReduction x :=
  equivOfCommonPresentation_apply _ _ _ _ _ x

end Parafree.TheoremB.Auxiliary
