import Parafree.Homology.SplitExtension.Mixed

/-! A split injection from coefficient H₁ to ordinary H₂.
Only a Lie section, an equivariant coefficient inclusion, and a crossed
retraction are needed. No freeness or higher-homology vanishing is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.Homology.Coefficients
open LieRings.Homological.LieHomology

variable (R G E V : Type*) [CommRing R] [LieRing G] [LieAlgebra R G]
  [LieRing E] [LieAlgebra R E] [AddCommGroup V] [Module R V]
  [LieRingModule G V]

structure SplitInjectionData where
  base : G →ₗ⁅R⁆ E
  quotient : E →ₗ⁅R⁆ G
  coefficientSection : V →ₗ[R] E
  projection : E →ₗ[R] V
  quotient_base : ∀ g, quotient (base g) = g
  quotient_section : ∀ v, quotient (coefficientSection v) = 0
  projection_section : ∀ v, projection (coefficientSection v) = v
  section_equivariant : ∀ g v, ⁅base g,coefficientSection v⁆ = coefficientSection ⁅g,v⁆
  projection_lie : ∀ x y, projection ⁅x,y⁆ = ⁅quotient x,projection y⁆ - ⁅quotient y,projection x⁆

namespace SplitInjectionData
variable {R G E V} [LieModule R G V] (S : SplitInjectionData R G E V)

private theorem pair_lie (g h : G) (v : V) :
    reducedPair R G V ⁅g,h⁆ v = reducedPair R G V g ⁅h,v⁆ - reducedPair R G V h ⁅g,v⁆ :=
  eq_sub_of_add_eq (sub_eq_zero.mp (reducedPair_relation R G V g h v))

def mixedBilinear : E →ₗ[R] E →ₗ[R] ReducedOne R G V :=
  let f := ((reducedPair R G V).compl₂ S.projection).comp S.quotient.toLinearMap
  f - f.flip

@[simp] theorem mixedBilinear_apply (x y : E) : S.mixedBilinear x y =
    reducedPair R G V (S.quotient x) (S.projection y) -
      reducedPair R G V (S.quotient y) (S.projection x) := rfl

theorem mixedBilinear_alt : S.mixedBilinear.IsAlt := by
  intro x
  rw [mixedBilinear_apply,sub_self]

theorem mixedBilinear_leibniz (x y z : E) :
    S.mixedBilinear x ⁅y,z⁆ = S.mixedBilinear ⁅x,y⁆ z + S.mixedBilinear y ⁅x,z⁆ := by
  simp only [mixedBilinear_apply,LieHom.map_lie,S.projection_lie,map_sub]
  rw [pair_lie,pair_lie,pair_lie]
  abel

def mixedMap : ReducedExteriorSquare R E →ₗ[R] ReducedOne R G V :=
  reducedExteriorLift R E S.mixedBilinear S.mixedBilinear_alt S.mixedBilinear_leibniz

@[simp] theorem mixedMap_wedge (x y : E) : S.mixedMap (reducedWedge R E x y) =
    reducedPair R G V (S.quotient x) (S.projection y) -
      reducedPair R G V (S.quotient y) (S.projection x) :=
  reducedExteriorLift_wedge R E _ _ _ x y

def insertionBilinear : G →ₗ[R] V →ₗ[R] ReducedExteriorSquare R E :=
  ((reducedWedge R E).compl₂ S.coefficientSection).comp S.base.toLinearMap

omit [LieModule R G V] in
@[simp] theorem insertionBilinear_apply (g : G) (v : V) :
    S.insertionBilinear g v = reducedWedge R E (S.base g) (S.coefficientSection v) := rfl

omit [LieModule R G V] in
theorem insertion_relation (g h : G) (v : V) :
    S.insertionBilinear ⁅g,h⁆ v + S.insertionBilinear h ⁅g,v⁆ - S.insertionBilinear g ⁅h,v⁆ = 0 := by
  simp only [insertionBilinear_apply,LieHom.map_lie]
  rw [← S.section_equivariant,← S.section_equivariant,
    reducedWedge_leibniz R E (S.base g) (S.base h) (S.coefficientSection v)]
  abel

def insertion : ReducedOne R G V →ₗ[R] ReducedExteriorSquare R E :=
  reducedOneLift R G V S.insertionBilinear S.insertion_relation

@[simp] theorem insertion_pair (g : G) (v : V) :
    S.insertion (reducedPair R G V g v) = reducedWedge R E (S.base g) (S.coefficientSection v) :=
  reducedOneLift_pair R G V _ _ g v

theorem mixedMap_insertion : S.mixedMap.comp S.insertion = LinearMap.id := by
  apply reducedOne_ext R G V
  intro g v
  change S.mixedMap (S.insertion (reducedPair R G V g v)) = reducedPair R G V g v
  rw [insertion_pair,mixedMap_wedge,S.quotient_base,S.projection_section,
    S.quotient_section,map_zero,LinearMap.zero_apply,sub_zero]

theorem bracket_insertion : (reducedBracket R E).comp S.insertion = S.coefficientSection.comp (reducedAction R G V) := by
  apply reducedOne_ext R G V
  intro g v
  change reducedBracket R E (S.insertion (reducedPair R G V g v)) = S.coefficientSection (reducedAction R G V (reducedPair R G V g v))
  rw [insertion_pair,reducedBracket_wedge,reducedAction_pair,S.section_equivariant]

theorem action_mixedMap : (reducedAction R G V).comp S.mixedMap = S.projection.comp (reducedBracket R E) := by
  apply reducedExteriorMap_ext R E
  intro x y
  change reducedAction R G V (S.mixedMap (reducedWedge R E x y)) = S.projection (reducedBracket R E (reducedWedge R E x y))
  rw [mixedMap_wedge,map_sub,reducedAction_pair,reducedAction_pair,reducedBracket_wedge,S.projection_lie]

def cycleInsertion : LinearMap.ker (reducedAction R G V) →ₗ[R] LinearMap.ker (reducedBracket R E) :=
  (S.insertion.comp (LinearMap.ker (reducedAction R G V)).subtype).codRestrict _ (fun z => by
    change reducedBracket R E (S.insertion z) = 0
    calc
      reducedBracket R E (S.insertion z) = S.coefficientSection (reducedAction R G V z) :=
        LinearMap.congr_fun S.bracket_insertion z
      _ = 0 := by rw [z.property,map_zero])

def cycleRetraction : LinearMap.ker (reducedBracket R E) →ₗ[R] LinearMap.ker (reducedAction R G V) :=
  (S.mixedMap.comp (LinearMap.ker (reducedBracket R E)).subtype).codRestrict _ (fun z => by
    change reducedAction R G V (S.mixedMap z) = 0
    calc
      reducedAction R G V (S.mixedMap z) = S.projection (reducedBracket R E z) :=
        LinearMap.congr_fun S.action_mixedMap z
      _ = 0 := by rw [z.property,map_zero])

theorem cycleRetraction_insertion (z : LinearMap.ker (reducedAction R G V)) :
    S.cycleRetraction (S.cycleInsertion z) = z :=
  Subtype.ext (LinearMap.congr_fun S.mixedMap_insertion z)

def ordinaryEquiv : LieRings.Homological.LieHomology.Homology (R := R) (L := E) 2 ≃ₗ[R]
    LinearMap.ker (reducedBracket R E) :=
  (secondHomologyConcreteIso R E).toLinearEquiv.trans (secondHomologyEquivReducedBracketKernel R E)

def homologyInjection : Homology R G V 1 →ₗ[R]
    LieRings.Homological.LieHomology.Homology (R := R) (L := E) 2 :=
  (ordinaryEquiv (R := R) (E := E)).symm.toLinearMap.comp
    (S.cycleInsertion.comp (homologyOneEquivReducedKernel R G V).toLinearMap)

def homologyRetraction : LieRings.Homological.LieHomology.Homology (R := R) (L := E) 2 →ₗ[R]
    Homology R G V 1 :=
  (homologyOneEquivReducedKernel R G V).symm.toLinearMap.comp
    (S.cycleRetraction.comp (ordinaryEquiv (R := R) (E := E)).toLinearMap)

theorem homologyRetraction_injection (z : Homology R G V 1) :
    S.homologyRetraction (S.homologyInjection z) = z := by
  simp only [homologyInjection,homologyRetraction,LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,LinearEquiv.apply_symm_apply,cycleRetraction_insertion,
    LinearEquiv.symm_apply_apply]

theorem homologyInjection_injective : Function.Injective S.homologyInjection :=
  Function.LeftInverse.injective S.homologyRetraction_injection

end SplitInjectionData
end Parafree.Homology.Coefficients
