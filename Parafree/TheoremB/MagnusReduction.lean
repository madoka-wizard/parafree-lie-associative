import Parafree.TheoremB.IntegralMagnus

/-! Reduction of the localized Magnus coordinates to the residue field.
Only universal properties of the auxiliary presentation and enveloping algebra
are used; no base-change injectivity of enveloping algebras is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB.MagnusReduction
open Parafree.Lie Parafree.Homology.Coefficients Auxiliary
abbrev R := AtFive
abbrev K := ZMod 5
abbrev G := Presented K
abbrev U := LieRings.UEA K G
abbrev V := FoxSequence.FreeCoefficients K (Fin 2) (relationIdeal K)
abbrev E := ModuleExtension G V

theorem denominator_unit (s : fiveIdeal.primeCompl) : IsUnit ((s:ℤ):K) := by
  apply isUnit_iff_ne_zero.mpr
  intro hs
  exact s.property (Ideal.mem_span_singleton.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd (s:ℤ) 5).mp hs))

def residue : R →+* K := IsLocalization.lift (g := Int.castRingHom K) denominator_unit

local instance : Algebra R K := residue.toAlgebra
local instance : Module R G := Module.compHom G residue
local instance : LieAlgebra R G where
  lie_smul r x y := lie_smul (residue r) x y
local instance : Algebra R U := Algebra.compHom U residue

def baseMapR : Presented R →ₗ⁅R⁆ G :=
  Auxiliary.lift (gen K 0) (gen K 1) (presented_f₁ K) (presented_f₂ K)

def baseMap : Presented R →ₗ⁅ℤ⁆ G :=
  { baseMapR.toLinearMap.restrictScalars ℤ with map_lie' := baseMapR.map_lie _ _ }

@[simp] theorem baseMap_gen (i : Fin 2) : baseMap (gen R i) = gen K i := by
  change baseMapR (gen R i) = _
  rw [baseMapR,Auxiliary.lift_gen]
  fin_cases i <;> rfl

def iotaR : G →ₗ⁅R⁆ U where
  toFun := UniversalEnvelopingAlgebra.ι K
  map_add' := map_add _
  map_smul' r x := by
    change UniversalEnvelopingAlgebra.ι K (residue r • x) = residue r • UniversalEnvelopingAlgebra.ι K x
    exact map_smul _ _ _
  map_lie' := (UniversalEnvelopingAlgebra.ι K).map_lie _ _

def enveloping : LieRings.UEA R (Presented R) →ₐ[R] U :=
  UniversalEnvelopingAlgebra.lift R (iotaR.comp baseMapR)

@[simp] theorem enveloping_iota (x : Presented R) :
    enveloping (UniversalEnvelopingAlgebra.ι R x) = UniversalEnvelopingAlgebra.ι K (baseMap x) := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply R (iotaR.comp baseMapR) x

def coefficientMap : IntegralMagnus.V →ₗ[ℤ] V :=
  ((FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K)).symm.toLinearMap.restrictScalars ℤ).comp
    ((Finsupp.mapRange.linearMap (enveloping.toLinearMap.restrictScalars ℤ)).comp
      ((FoxSequence.freeCoordinates R (Fin 2) (relationIdeal R)).toLinearMap.restrictScalars ℤ))

@[simp] theorem coefficientMap_apply (v : IntegralMagnus.V) (i : Fin 2) :
    FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K) (coefficientMap v) i =
      enveloping (FoxSequence.freeCoordinates R (Fin 2) (relationIdeal R) v i) := by
  change (FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K)
    ((FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K)).symm _)) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem coefficientMap_lie (g : Presented R) (v : IntegralMagnus.V) :
    coefficientMap ⁅g,v⁆ = ⁅baseMap g,coefficientMap v⁆ := by
  apply (FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K)).injective
  ext i
  rw [coefficientMap_apply]
  change enveloping (UniversalEnvelopingAlgebra.ι R g *
    FoxSequence.freeCoordinates R (Fin 2) (relationIdeal R) v i) =
    UniversalEnvelopingAlgebra.ι K (baseMap g) *
      FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K) (coefficientMap v) i
  rw [map_mul,enveloping_iota,coefficientMap_apply]

def hom : IntegralMagnus.E →ₗ⁅ℤ⁆ E where
  toFun x := ⟨baseMap x.base,coefficientMap x.coefficient⟩
  map_add' x y := by apply ModuleExtension.ext <;> exact map_add _ _ _
  map_smul' c x := by apply ModuleExtension.ext <;> exact map_smul _ _ _
  map_lie' {x y} := by
    apply ModuleExtension.ext
    · exact baseMap.map_lie _ _
    · exact (map_sub coefficientMap _ _).trans (congrArg₂ (·-·)
        (coefficientMap_lie _ _) (coefficientMap_lie _ _))

def fieldIntegral : IntegralFree →ₗ⁅ℤ⁆ E :=
  ({ (FoxSequence.magnus K (Fin 2) (relationIdeal K)).toLinearMap.restrictScalars ℤ with
    map_lie' := (FoxSequence.magnus K (Fin 2) (relationIdeal K)).map_lie _ _ } :
      Free K →ₗ⁅ℤ⁆ E).comp ambientReduction

@[simp] theorem fieldIntegral_generator (i : Fin 2) :
    fieldIntegral (Auxiliary.generator ℤ i) = FoxSequence.magnus K (Fin 2) (relationIdeal K) (Auxiliary.generator K i) := by
  change FoxSequence.magnus K (Fin 2) (relationIdeal K) (ambientReduction (Auxiliary.generator ℤ i)) = _
  rw [ambientReduction_generator]

theorem hom_integral (z : IntegralFree) : hom (IntegralMagnus.integral z) = fieldIntegral z := by
  have he : hom.comp IntegralMagnus.integral = fieldIntegral := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change hom (IntegralMagnus.integral (Auxiliary.generator ℤ i)) = fieldIntegral (Auxiliary.generator ℤ i)
    rw [IntegralMagnus.integral_generator,fieldIntegral_generator]
    apply ModuleExtension.ext
    · exact baseMap_gen i
    · apply (FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K)).injective
      ext j
      change FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K)
        (coefficientMap (FoxSequence.crossedDerivative R (Fin 2) (relationIdeal R) (FreeLieAlgebra.of R i))) j =
          FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K)
            (FoxSequence.crossedDerivative K (Fin 2) (relationIdeal K) (FreeLieAlgebra.of K i)) j
      rw [coefficientMap_apply,FoxSequence.crossedDerivative_generator,FoxSequence.crossedDerivative_generator]
      classical
      by_cases hij : i=j <;> simp [hij]
  exact LieHom.congr_fun he z

theorem hom_scaled (z : IntegralFree) :
    hom (IntegralMagnus.scaled z) = ⟨(fieldIntegral z).base,0⟩ := by
  apply ModuleExtension.ext
  · have he := congrArg (fun x : E => x.base) (hom_integral z)
    exact he
  · change coefficientMap ((5:R) • (IntegralMagnus.integral z).coefficient) = 0
    rw [show (5:R) • (IntegralMagnus.integral z).coefficient =
      (5:ℤ) • (IntegralMagnus.integral z).coefficient by
        simpa only [Int.cast_ofNat] using Int.cast_smul_eq_zsmul R (5:ℤ) (IntegralMagnus.integral z).coefficient]
    rw [map_smul,← Int.cast_smul_eq_zsmul K,show ((5:ℤ):K)=0 by decide,zero_smul]

theorem hom_relationImage (r : relationIdeal ℤ) :
    hom (IntegralMagnus.relationImage r) = ⟨0,(fieldIntegral r).coefficient⟩ := by
  apply ModuleExtension.ext
  · exact map_zero baseMap
  · have he := congrArg (fun x : E => x.coefficient) (hom_integral r)
    exact he

theorem fieldIntegral_relation (r : relationIdeal ℤ) :
    (fieldIntegral r).coefficient = (relationCoefficientEquiv (Submodule.Quotient.mk (relationReduction r)) : V) := by
  apply (FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K)).injective
  change FoxSequence.freeCoordinates K (Fin 2) (relationIdeal K)
    (FoxSequence.crossedDerivative K (Fin 2) (relationIdeal K) (relationReduction r)) = _
  rw [FoxSequence.crossedDerivative_relation]
  rfl

end Parafree.TheoremB.MagnusReduction
