import Parafree.TheoremB.CoefficientSection
import Parafree.Homology.Coefficients.Magnus
import Parafree.Lie.InjectiveDescent
import Mathlib.RingTheory.Flat.TorsionFree

/-! A rational Magnus representation whose values on the four generators of
P lie in the localization at five. Scaling the free coefficients by five is
what makes the divided relators integral in this representation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB.IntegralMagnus
open Parafree.Lie Parafree.Homology.Coefficients Auxiliary
open scoped TensorProduct

abbrev R := AtFive
abbrev G := Presented R
abbrev V := FoxSequence.FreeCoefficients R (Fin 2) (relationIdeal R)
abbrev E := ModuleExtension G V

instance scalar_charZero : CharZero R :=
  charZero_of_injective_algebraMap (IsLocalization.injective R fiveIdeal.primeCompl_le_nonZeroDivisors)

instance enveloping_free : Module.Free R (LieRings.UEA R G) := by
  let b := Module.Free.chooseBasis R G
  letI : LinearOrder (Module.Free.ChooseBasisIndex R G) := IsWellFounded.wellOrderExtension emptyWf.rel
  exact Module.Free.of_equiv (Parafree.Associative.FilteredPBW.equiv b)

instance coefficients_free : Module.Free R V :=
  Module.Free.of_equiv (FoxSequence.freeCoordinates R (Fin 2) (relationIdeal R)).symm

instance extension_int_torsionFree : Module.IsTorsionFree ℤ E := by
  letI : Module.IsTorsionFree R E := (Module.Free.chooseBasis R E).isTorsionFree
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n x hx
  have h : (n:R) • x = 0 := by simpa only [Int.cast_smul_eq_zsmul] using hx
  rcases (smul_eq_zero.mp h) with hn | hx
  · exact Or.inl (Int.cast_injective (by simpa using hn))
  · exact Or.inr hx

abbrev rationalUnit : E →ₗ⁅ℤ⁆ (ℚ ⊗[ℤ] E) := FreeScalarExtension.unit ℚ

theorem rationalUnit_injective : Function.Injective rationalUnit := FreeScalarExtension.unit_injective ℚ

def integral : IntegralFree →ₗ⁅ℤ⁆ E :=
  ({ (FoxSequence.magnus R (Fin 2) (relationIdeal R)).toLinearMap.restrictScalars ℤ with
    map_lie' := (FoxSequence.magnus R (Fin 2) (relationIdeal R)).map_lie _ _ } :
      Free R →ₗ⁅ℤ⁆ E).comp
      (FreeScalarExtension.generatorMap R (Fin 2))

@[simp] theorem integral_generator (i : Fin 2) :
    integral (Auxiliary.generator ℤ i) = FoxSequence.magnus R (Fin 2) (relationIdeal R) (Auxiliary.generator R i) := by
  change FoxSequence.magnus R (Fin 2) (relationIdeal R)
    (FreeScalarExtension.generatorMap R (Fin 2) (FreeLieAlgebra.of ℤ i)) = _
  rw [FreeScalarExtension.generatorMap_of]
  rfl

theorem integral_base (z : IntegralFree) :
    (integral z).base = integralMap R (quotientMk (relationIdeal ℤ) z) := by
  let q : E →ₗ⁅ℤ⁆ G :=
    { (ModuleExtension.projection R G V).toLinearMap.restrictScalars ℤ with
      map_lie' := (ModuleExtension.projection R G V).map_lie _ _ }
  have he : q.comp integral = (integralMap R).comp (quotientMk (relationIdeal ℤ)) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change quotientMk (relationIdeal R)
      (FreeScalarExtension.generatorMap R (Fin 2) (FreeLieAlgebra.of ℤ i)) = integralMap R (gen ℤ i)
    rw [FreeScalarExtension.generatorMap_of,integralMap_gen]
    rfl
  exact LieHom.congr_fun he z

theorem integral_relation_base (r : relationIdeal ℤ) : (integral r).base = 0 := by
  rw [integral_base,(quotientMk_eq_zero _ _).mpr r.property,map_zero]

def scaled : IntegralFree →ₗ⁅ℤ⁆ E :=
  ({ (ModuleExtension.scale R G V (5:R)).toLinearMap.restrictScalars ℤ with
    map_lie' := (ModuleExtension.scale R G V (5:R)).map_lie _ _ } : E →ₗ⁅ℤ⁆ E).comp integral

def rational : Ambient →ₗ⁅ℚ⁆ (ℚ ⊗[ℤ] E) :=
  FreeLieAlgebra.lift ℚ (fun i => rationalUnit (scaled (FreeLieAlgebra.of ℤ i)))

def rationalInt : Ambient →ₗ⁅ℤ⁆ (ℚ ⊗[ℤ] E) :=
  { rational.toLinearMap.restrictScalars ℤ with map_lie' := rational.map_lie _ _ }

theorem rational_integral (z : IntegralFree) : rational (DividedModel.inclusion z) = rationalUnit (scaled z) := by
  have he : rationalInt.comp DividedModel.inclusion = rationalUnit.comp scaled := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change rational (DividedModel.inclusion (FreeLieAlgebra.of ℤ i)) = rationalUnit (scaled (FreeLieAlgebra.of ℤ i))
    rw [show DividedModel.inclusion (FreeLieAlgebra.of ℤ i) = FreeLieAlgebra.of ℚ i from DividedModel.inclusion_generator i]
    exact FreeLieAlgebra.lift_of_apply _ _
  exact LieHom.congr_fun he z

def relationImage (r : relationIdeal ℤ) : E := ⟨0,(integral r).coefficient⟩

theorem scaled_relation (r : relationIdeal ℤ) : scaled r = (5:ℤ) • relationImage r := by
  apply ModuleExtension.ext
  · change (integral r).base = (5:ℤ) • (0:G)
    rw [integral_relation_base,smul_zero]
  · change (5:R) • (integral r).coefficient = (5:ℤ) • (integral r).coefficient
    simpa only [Int.cast_ofNat] using Int.cast_smul_eq_zsmul R (5:ℤ) (integral r).coefficient

theorem rational_divided (r : relationIdeal ℤ) :
    rational ((1/5:ℚ) • DividedModel.inclusion r) = rationalUnit (relationImage r) := by
  rw [map_smul,rational_integral,scaled_relation,map_zsmul,← Int.cast_smul_eq_zsmul ℚ,smul_smul]
  norm_num

def integralRelator (i : Fin 2) : relationIdeal ℤ :=
  ⟨relator ℤ i,LieSubmodule.subset_lieSpan (Set.mem_range_self i)⟩

def generatorImage : Fin 4 → E :=
  ![scaled (Auxiliary.generator ℤ 0),scaled (Auxiliary.generator ℤ 1),
    relationImage (integralRelator 0),relationImage (integralRelator 1)]

theorem rational_generator (i : Fin 4) :
    rational (generators i) = rationalUnit (generatorImage i) := by
  fin_cases i
  · exact FreeLieAlgebra.lift_of_apply _ _
  · exact FreeLieAlgebra.lift_of_apply _ _
  · change rational ((1/5:ℚ) • f₁ ambientT ambientA) = rationalUnit (relationImage (integralRelator 0))
    have h := rational_divided (integralRelator 0)
    simpa only [integralRelator,DividedModel.inclusion_relator,Matrix.cons_val_zero] using h
  · change rational ((1/5:ℚ) • f₂ ambientT ambientA) = rationalUnit (relationImage (integralRelator 1))
    have h := rational_divided (integralRelator 1)
    simpa only [integralRelator,DividedModel.inclusion_relator,Matrix.cons_val_one] using h

theorem rational_mem (x : P) : rationalInt x ∈ rationalUnit.range := by
  have he : algebra ≤ rationalUnit.range.comap rationalInt := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨generatorImage i,(rational_generator i).symm⟩
  exact he x.property

/-- The actual map on the rational subring in the manuscript. -/
def hom : P →ₗ⁅ℤ⁆ E :=
  InjectiveDescent.hom rationalUnit rationalUnit_injective
    (rationalInt.comp algebra.incl) rational_mem

@[simp] theorem hom_triangle (x : P) : rationalUnit (hom x) = rational x :=
  InjectiveDescent.triangle _ _ _ _ x

@[simp] theorem hom_generator (i : Fin 4) : hom (TheoremB.generator i) = generatorImage i := by
  apply rationalUnit_injective
  rw [hom_triangle]
  exact rational_generator i

theorem hom_integralLift (x : IntegralFree) : hom (DividedModel.integralLift x) = scaled x := by
  apply rationalUnit_injective
  rw [hom_triangle,DividedModel.integralLift_coe,rational_integral]

theorem hom_divide (r : relationIdeal ℤ) : hom (DividedModel.divide r) = relationImage r := by
  apply rationalUnit_injective
  rw [hom_triangle,DividedModel.divide_coe,rational_divided]

end Parafree.TheoremB.IntegralMagnus
