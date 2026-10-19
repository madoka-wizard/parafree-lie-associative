import Parafree.Homology.SplitExtension.Generation

/-! The low-degree split-extension comparison.  It is proved using the actual
CE reduced exterior square and coefficient CE boundaries, over any commutative
ring.  The only vanishing assumptions are on second homology of the base and
of the kernel. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Parafree.Homology.SplitExtension.Data

open LieRings.Homological.LieHomology
open Coefficients

attribute [local instance] reducedExteriorAddCommMonoid

variable {R G E V : Type*} [CommRing R] [LieRing G] [LieAlgebra R G]
  [LieRing E] [LieAlgebra R E] [AddCommGroup V] [Module R V]
  [LieRingModule G V] [LieModule R G V]

variable (S : SplitExtension.Data R G E V)

theorem mixedMap_insertion : S.mixedMap.comp S.mixedInsertion = LinearMap.id := by
  apply reducedOne_ext R G V
  intro g v
  change S.mixedMap (S.mixedInsertion (reducedPair R G V g v)) = reducedPair R G V g v
  rw [mixedInsertion_pair, mixedMap_mixed, S.projection_section]

theorem bracket_insertion : (reducedBracket R E).comp S.mixedInsertion =
    S.ideal.incl.toLinearMap.comp (S.coefficientSection.comp (reducedAction R G V)) := by
  apply reducedOne_ext R G V
  intro g v
  change reducedBracket R E (S.mixedInsertion (reducedPair R G V g v)) =
    (S.coefficientSection (reducedAction R G V (reducedPair R G V g v)) : E)
  rw [mixedInsertion_pair, reducedBracket_wedge, reducedAction_pair, section_lie_coe]

theorem action_mixedMap : (reducedAction R G V).comp S.mixedMap =
    S.abelianPart.comp (reducedBracket R E) := by
  apply reducedExteriorMap_ext R E
  intro x y
  change reducedAction R G V (S.mixedMap (reducedWedge R E x y)) =
    S.abelianPart (reducedBracket R E (reducedWedge R E x y))
  rw [mixedMap_wedge, map_sub, reducedAction_pair, reducedAction_pair,
    reducedBracket_wedge, abelianPart_lie]

def cyclesToMixed : LinearMap.ker (reducedBracket R E) →ₗ[R]
    LinearMap.ker (reducedAction R G V) :=
  (S.mixedMap.comp (LinearMap.ker (reducedBracket R E)).subtype).codRestrict _ (fun z => by
    change reducedAction R G V (S.mixedMap z) = 0
    calc
      reducedAction R G V (S.mixedMap z) = S.abelianPart (reducedBracket R E z) :=
        LinearMap.congr_fun S.action_mixedMap z
      _ = 0 := by rw [z.property, map_zero])

theorem cyclesToMixed_surjective : Function.Surjective S.cyclesToMixed := by
  intro z
  have hz : reducedBracket R E (S.mixedInsertion z) = 0 := by
    calc
      reducedBracket R E (S.mixedInsertion z) = (S.coefficientSection (reducedAction R G V z) : E) :=
        LinearMap.congr_fun S.bracket_insertion z
      _ = 0 := by rw [z.property, map_zero]; rfl
  exact ⟨⟨S.mixedInsertion z,hz⟩, Subtype.ext (LinearMap.congr_fun S.mixedMap_insertion z)⟩

variable [Subsingleton (LieRings.Homological.LieHomology.Homology (R := R) (L := G) 2)]
  [Subsingleton (LieRings.Homological.LieHomology.Homology (R := R) (L := S.ideal) 2)]

theorem cyclesToMixed_injective : Function.Injective S.cyclesToMixed := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  have hm : S.mixedMap z = 0 := congrArg Subtype.val hz
  have hq : S.quotientMap z = 0 := by
    apply ReducedExterior.bracket_injective_of_homologyTwo_zero
    rw [map_zero]
    calc
      reducedBracket R G (S.quotientMap z) = S.quotient (reducedBracket R E z) :=
        (LinearMap.congr_fun (reducedBracket_natural R S.quotient) z).symm
      _ = 0 := by rw [z.property, map_zero]
  have hd : S.defect z = z := by rw [defect_apply, hq, hm, map_zero, map_zero, sub_zero, sub_zero]
  obtain ⟨t,ht⟩ := hd ▸ S.defect_mem_range z
  have htzero : reducedBracket R S.ideal t = 0 := by
    apply S.ideal.incl_injective
    rw [map_zero]
    calc
      S.ideal.incl (reducedBracket R S.ideal t) = reducedBracket R E (S.idealMap t) :=
        LinearMap.congr_fun (reducedBracket_natural R S.ideal.incl) t
      _ = 0 := by rw [ht]; exact z.property
  have ht0 : t = 0 := ReducedExterior.bracket_injective_of_homologyTwo_zero
    (htzero.trans (map_zero _).symm)
  have hz0 : (z : ReducedExteriorSquare R E) = 0 := by rw [← ht, ht0, map_zero]
  exact Subtype.ext hz0

/-- The actual second CE homology of the extension is the actual first CE
homology of the base with coefficients in the split kernel abelianization. -/
def homologyTwoEquivOne :
    LieRings.Homological.LieHomology.Homology (R := R) (L := E) 2 ≃ₗ[R] Coefficients.Homology R G V 1 :=
  (secondHomologyConcreteIso R E).toLinearEquiv.trans
    ((secondHomologyEquivReducedBracketKernel R E).trans
      ((LinearEquiv.ofBijective S.cyclesToMixed
        ⟨S.cyclesToMixed_injective,S.cyclesToMixed_surjective⟩).trans
          (homologyOneEquivReducedKernel R G V).symm))

end Parafree.Homology.SplitExtension.Data
