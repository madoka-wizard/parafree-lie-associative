import Parafree.Homology.SplitExtension.Data

/-! The maps between reduced exterior squares and actual coefficient one-chains
modulo boundaries.  Both descent proofs check the CE relations explicitly. -/

noncomputable section
namespace Parafree.Homology.SplitExtension.Data

open LieRings.Homological.LieHomology
open Coefficients

variable {R G E V : Type*} [CommRing R] [LieRing G] [LieAlgebra R G]
  [LieRing E] [LieAlgebra R E] [AddCommGroup V] [Module R V]
  [LieRingModule G V] [LieModule R G V]

variable (S : Data R G E V)

theorem reducedPair_lie (g h : G) (v : V) :
    reducedPair R G V ⁅g,h⁆ v = reducedPair R G V g ⁅h,v⁆ - reducedPair R G V h ⁅g,v⁆ :=
  eq_sub_of_add_eq (sub_eq_zero.mp (reducedPair_relation R G V g h v))

def mixedBilinear : E →ₗ[R] E →ₗ[R] ReducedOne R G V :=
  let f := ((reducedPair R G V).compl₂ S.abelianPart).comp S.quotient.toLinearMap
  f - f.flip

@[simp] theorem mixedBilinear_apply (x y : E) : S.mixedBilinear x y =
    reducedPair R G V (S.quotient x) (S.abelianPart y) -
      reducedPair R G V (S.quotient y) (S.abelianPart x) := rfl

theorem mixedBilinear_alt : S.mixedBilinear.IsAlt := by
  intro x
  rw [mixedBilinear_apply, sub_self]

theorem mixedBilinear_leibniz (x y z : E) :
    S.mixedBilinear x ⁅y,z⁆ = S.mixedBilinear ⁅x,y⁆ z + S.mixedBilinear y ⁅x,z⁆ := by
  simp only [mixedBilinear_apply, LieHom.map_lie, abelianPart_lie, map_sub]
  rw [reducedPair_lie, reducedPair_lie, reducedPair_lie]
  abel

def mixedMap : ReducedExteriorSquare R E →ₗ[R] ReducedOne R G V :=
  reducedExteriorLift R E S.mixedBilinear S.mixedBilinear_alt S.mixedBilinear_leibniz

@[simp] theorem mixedMap_wedge (x y : E) : S.mixedMap (reducedWedge R E x y) =
    reducedPair R G V (S.quotient x) (S.abelianPart y) -
      reducedPair R G V (S.quotient y) (S.abelianPart x) :=
  reducedExteriorLift_wedge R E _ _ _ x y

@[simp] theorem mixedMap_base (g h : G) :
    S.mixedMap (reducedWedge R E (S.base g) (S.base h)) = 0 := by
  rw [mixedMap_wedge, abelianPart_base, abelianPart_base, map_zero, map_zero, sub_self]

@[simp] theorem mixedMap_ideal (f t : S.ideal) :
    S.mixedMap (reducedWedge R E (f : E) (t : E)) = 0 := by
  rw [mixedMap_wedge, S.quotient_ideal, S.quotient_ideal, map_zero]
  rfl

@[simp] theorem mixedMap_mixed (g : G) (f : S.ideal) :
    S.mixedMap (reducedWedge R E (S.base g) (f : E)) = reducedPair R G V g (S.projection f) := by
  rw [mixedMap_wedge, S.quotient_base, S.quotient_ideal, abelianPart_ideal, map_zero]
  exact sub_zero _

def mixedInsertionBilinear : G →ₗ[R] V →ₗ[R] ReducedExteriorSquare R E :=
  ((reducedWedge R E).compl₂ (S.ideal.incl.toLinearMap.comp S.coefficientSection)).comp S.base.toLinearMap

omit [LieModule R G V] in
@[simp] theorem mixedInsertionBilinear_apply (g : G) (v : V) :
    S.mixedInsertionBilinear g v = reducedWedge R E (S.base g) (S.coefficientSection v : E) := rfl

omit [LieModule R G V] in
theorem section_lie_coe (g : G) (v : V) :
    ⁅S.base g,(S.coefficientSection v : E)⁆ = (S.coefficientSection ⁅g,v⁆ : E) :=
  congrArg Subtype.val (S.section_equivariant g v)

omit [LieModule R G V] in
theorem mixedInsertion_relation (g h : G) (v : V) :
    S.mixedInsertionBilinear ⁅g,h⁆ v + S.mixedInsertionBilinear h ⁅g,v⁆ -
      S.mixedInsertionBilinear g ⁅h,v⁆ = 0 := by
  simp only [mixedInsertionBilinear_apply, LieHom.map_lie]
  rw [← section_lie_coe, ← section_lie_coe,
    reducedWedge_leibniz R E (S.base g) (S.base h) (S.coefficientSection v : E)]
  abel

def mixedInsertion : ReducedOne R G V →ₗ[R] ReducedExteriorSquare R E :=
  reducedOneLift R G V S.mixedInsertionBilinear S.mixedInsertion_relation

@[simp] theorem mixedInsertion_pair (g : G) (v : V) :
    S.mixedInsertion (reducedPair R G V g v) = reducedWedge R E (S.base g) (S.coefficientSection v : E) :=
  reducedOneLift_pair R G V _ _ g v

end Parafree.Homology.SplitExtension.Data
