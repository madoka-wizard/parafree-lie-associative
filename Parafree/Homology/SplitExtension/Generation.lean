import Parafree.Homology.SplitExtension.Mixed

/-! Modulo the image of the kernel's reduced exterior square, every reduced
two-chain is its base part plus its mixed coefficient part. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Parafree.Homology.SplitExtension.Data

open LieRings.Homological.LieHomology
open Coefficients Parafree.Lie

variable {R G E V : Type*} [CommRing R] [LieRing G] [LieAlgebra R G]
  [LieRing E] [LieAlgebra R E] [AddCommGroup V] [Module R V]
  [LieRingModule G V] [LieModule R G V]

variable (S : Data R G E V)

-- Use the canonical quotient structure directly in the bilinear calculations.
local instance reducedExteriorAddCommMonoid (W : Type*) [LieRing W] [LieAlgebra R W] :
    AddCommMonoid (ReducedExteriorSquare R W) :=
  (Submodule.Quotient.addCommGroup _).toAddCommMonoid

def baseMap : ReducedExteriorSquare R G →ₗ[R] ReducedExteriorSquare R E :=
  reducedExteriorMap (R := R) S.base

def quotientMap : ReducedExteriorSquare R E →ₗ[R] ReducedExteriorSquare R G :=
  reducedExteriorMap (R := R) S.quotient

def idealMap : ReducedExteriorSquare R S.ideal →ₗ[R] ReducedExteriorSquare R E :=
  reducedExteriorMap (R := R) S.ideal.incl

omit [LieModule R G V] in
theorem mixed_derived_mem_range (g : G) {f : S.ideal}
    (hf : f ∈ derivedSubmodule R S.ideal) :
    reducedWedge R E (S.base g) (f : E) ∈ S.idealMap.range := by
  rw [derivedSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hf
  refine Submodule.span_induction
    (p := fun (f : S.ideal) _ => reducedWedge R E (S.base g) (f : E) ∈ S.idealMap.range) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨a,_,b,_,rfl⟩
    refine ⟨reducedWedge R S.ideal ⁅S.base g,a⁆ b +
      reducedWedge R S.ideal a ⁅S.base g,b⁆, ?_⟩
    change S.idealMap _ = _
    rw [LinearMap.map_add]
    change reducedExteriorMap (R := R) S.ideal.incl (reducedWedge R S.ideal ⁅S.base g,a⁆ b) +
      reducedExteriorMap (R := R) S.ideal.incl (reducedWedge R S.ideal a ⁅S.base g,b⁆) = _
    rw [reducedExteriorMap_wedge, reducedExteriorMap_wedge]
    exact (reducedWedge_leibniz R E (S.base g) (a : E) (b : E)).symm
  · change reducedWedge R E (S.base g) 0 ∈ S.idealMap.range
    rw [LinearMap.map_zero]; exact S.idealMap.range.zero_mem
  · intro a b _ _ ha hb
    change reducedWedge R E (S.base g) ((a : E)+(b : E)) ∈ _
    rw [LinearMap.map_add]; exact S.idealMap.range.add_mem ha hb
  · intro r a _ ha
    change reducedWedge R E (S.base g) (r • (a : E)) ∈ _
    rw [LinearMap.map_smul]; exact S.idealMap.range.smul_mem r ha

def defect : ReducedExteriorSquare R E →ₗ[R] ReducedExteriorSquare R E :=
  LinearMap.id - S.baseMap.comp S.quotientMap - S.mixedInsertion.comp S.mixedMap

@[simp] theorem defect_apply (z : ReducedExteriorSquare R E) :
    S.defect z = z - S.baseMap (S.quotientMap z) - S.mixedInsertion (S.mixedMap z) := rfl

@[simp] theorem defect_base (g h : G) : S.defect (reducedWedge R E (S.base g) (S.base h)) = 0 := by
  rw [defect_apply, mixedMap_base, LinearMap.map_zero, sub_zero]
  change reducedWedge R E (S.base g) (S.base h) -
    reducedExteriorMap (R := R) S.base (reducedExteriorMap (R := R) S.quotient _) = 0
  rw [reducedExteriorMap_wedge, S.quotient_base, S.quotient_base, reducedExteriorMap_wedge, sub_self]

@[simp] theorem defect_ideal (f t : S.ideal) :
    S.defect (reducedWedge R E (f : E) (t : E)) = S.idealMap (reducedWedge R S.ideal f t) := by
  rw [defect_apply, mixedMap_ideal, LinearMap.map_zero, sub_zero]
  change reducedWedge R E (f : E) (t : E) -
    reducedExteriorMap (R := R) S.base (reducedExteriorMap (R := R) S.quotient _) = reducedExteriorMap (R := R) S.ideal.incl _
  rw [reducedExteriorMap_wedge, S.quotient_ideal, reducedWedge_zero_left, LinearMap.map_zero,
    sub_zero, reducedExteriorMap_wedge]
  rfl

theorem defect_mixed_mem_range (g : G) (f : S.ideal) :
    S.defect (reducedWedge R E (S.base g) (f : E)) ∈ S.idealMap.range := by
  have hd : f - S.coefficientSection (S.projection f) ∈ derivedSubmodule R S.ideal :=
    (S.projection_ker _).mp (by rw [LinearMap.map_sub, S.projection_section, sub_self])
  have hh := S.mixed_derived_mem_range g hd
  rw [defect_apply, mixedMap_mixed, mixedInsertion_pair]
  change reducedWedge R E (S.base g) (f : E) -
    reducedExteriorMap (R := R) S.base (reducedExteriorMap (R := R) S.quotient _) - _ ∈ _
  rw [reducedExteriorMap_wedge, S.quotient_ideal, reducedWedge_zero_right, LinearMap.map_zero, sub_zero]
  exact (LinearMap.map_sub (reducedWedge R E (S.base g)) (f : E) (S.coefficientSection (S.projection f) : E)) ▸ hh

theorem defect_wedge_mem_range (x y : E) : S.defect (reducedWedge R E x y) ∈ S.idealMap.range := by
  have hxy : reducedWedge R E x y =
      reducedWedge R E (S.base (S.quotient x)) (S.base (S.quotient y)) +
      reducedWedge R E (S.base (S.quotient x)) (S.part y : E) +
      reducedWedge R E (S.part x : E) (S.base (S.quotient y)) +
      reducedWedge R E (S.part x : E) (S.part y : E) := by
    conv_lhs => rw [S.decomposition x, S.decomposition y]
    simp only [LinearMap.map_add, LinearMap.add_apply, add_assoc]
    congr 1
    exact add_left_comm _ _ _
  rw [hxy, LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, defect_base, zero_add]
  apply S.idealMap.range.add_mem
  · apply S.idealMap.range.add_mem
    · exact S.defect_mixed_mem_range _ _
    · rw [reducedWedge_skew R E (S.part x : E) (S.base (S.quotient y)), LinearMap.map_neg]
      exact (S.idealMap.range).neg_mem (S.defect_mixed_mem_range _ _)
  · rw [defect_ideal]
    exact LinearMap.mem_range_self _ _

/-- The remaining part always comes from the actual reduced exterior square of
 the ideal; this is the chain-level generation statement for the comparison. -/
theorem defect_mem_range (z : ReducedExteriorSquare R E) : S.defect z ∈ S.idealMap.range := by
  obtain ⟨c,rfl⟩ := (thirdBoundaries R E).mkQ_surjective z
  have hc : c ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun c _ => S.defect (reducedClass R E c) ∈ S.idealMap.range) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨v,rfl⟩
    have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
    rw [hv]
    exact S.defect_wedge_mem_range (v 0) (v 1)
  · simp only [LinearMap.map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [LinearMap.map_add, LinearMap.map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha
    rw [LinearMap.map_smul, LinearMap.map_smul]; exact Submodule.smul_mem _ r ha

end Parafree.Homology.SplitExtension.Data
