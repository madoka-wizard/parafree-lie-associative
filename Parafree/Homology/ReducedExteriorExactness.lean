import LieRings.Homological.LieHomology.Presentation
import Parafree.Lie.Quotient

/-! Exactness of reduced exterior squares, with representative-level bracket formulas.
These lemmas provide the part of the five-term sequence needed for lower-central
comparison without introducing a second model of homology. -/

noncomputable section
namespace Parafree.Homology.ReducedExterior

open LieRings.Homological.LieHomology
open Parafree.Lie

variable {R : Type*} [CommRing R]
variable {L M N : Type*} [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N]

@[simp] theorem map_id :
    reducedExteriorMap (R := R) (LieHom.id : L →ₗ⁅R⁆ L) = LinearMap.id := by
  apply reducedExteriorMap_ext R L
  intro x y
  simp only [reducedExteriorMap_wedge, LieHom.id_apply, LinearMap.id_apply]

theorem map_comp (g : M →ₗ⁅R⁆ N) (f : L →ₗ⁅R⁆ M) :
    reducedExteriorMap (R := R) (g.comp f) = (reducedExteriorMap (R := R) g).comp (reducedExteriorMap (R := R) f) := by
  apply reducedExteriorMap_ext R L
  intro x y
  simp only [LinearMap.comp_apply, reducedExteriorMap_wedge, LieHom.comp_apply]

theorem map_bijective (f : L →ₗ⁅R⁆ M) (hf : Function.Bijective f) :
    Function.Bijective (reducedExteriorMap (R := R) f) := by
  let e := LieEquiv.ofBijective f hf
  have hleft : (reducedExteriorMap (R := R) e.symm.toLieHom).comp (reducedExteriorMap (R := R) f) =
      LinearMap.id := by
    rw [← map_comp]
    have h : e.symm.toLieHom.comp f = LieHom.id := by
      ext x
      exact e.symm_apply_apply x
    rw [h, map_id]
  have hright : (reducedExteriorMap (R := R) f).comp (reducedExteriorMap (R := R) e.symm.toLieHom) =
      LinearMap.id := by
    rw [← map_comp]
    have h : f.comp e.symm.toLieHom = LieHom.id := by
      ext x
      exact e.apply_symm_apply x
    rw [h, map_id]
  exact ⟨(fun x y h => by
    have := congrArg (reducedExteriorMap (R := R) e.symm.toLieHom) h
    simpa only [← LinearMap.comp_apply, hleft, LinearMap.id_apply] using this),
    fun y => ⟨reducedExteriorMap (R := R) e.symm.toLieHom y, LinearMap.congr_fun hright y⟩⟩

set_option synthInstance.maxHeartbeats 100000 in
/-- The exact kernel for every surjective Lie homomorphism. -/
theorem map_eq_zero_iff (p : L →ₗ⁅R⁆ M) (hp : Function.Surjective p)
    (z : ReducedExteriorSquare R L) :
    reducedExteriorMap (R := R) p z = 0 ↔ z ∈ relationWedges R p := by
  have hi : Function.Injective (presentationQuotientToReducedExterior R p) :=
    (reducedExteriorPresentationEquiv R p hp).symm.injective
  constructor
  · intro h
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply hi
    rw [map_zero]
    exact (presentationQuotientToReducedExterior_class R p z).trans h
  · intro h
    rw [← presentationQuotientToReducedExterior_class]
    have hz : relationClass R p z = 0 := (Submodule.Quotient.mk_eq_zero _).mpr h
    rw [hz, map_zero]

/-- The reduced bracket maps the relation-wedge submodule onto the commutator
with the kernel. This equality includes both the generation and lifting claims. -/
theorem bracket_relationWedges (I : LieIdeal R L) :
    (relationWedges R (quotientMk I)).map (reducedBracket R L) =
      (⁅(⊤ : LieIdeal R L), I⁆).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine Submodule.span_induction (p := fun z _ =>
      reducedBracket R L z ∈ (⁅(⊤ : LieIdeal R L), I⁆).toSubmodule) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨r, hr, x, rfl⟩
      have hrI : r ∈ I := (quotientMk_eq_zero I r).mp hr
      rw [reducedBracket_wedge, ← lie_skew r x]
      exact (⁅(⊤ : LieIdeal R L), I⁆).neg_mem
        (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hrI)
    · simp
    · intro a b _ _ ha hb
      simpa only [map_add] using (⁅(⊤ : LieIdeal R L), I⁆).add_mem ha hb
    · intro r a _ ha
      simpa only [map_smul] using (⁅(⊤ : LieIdeal R L), I⁆).smul_mem r ha
  · rw [LieSubmodule.lieIdeal_oper_eq_linear_span', Submodule.span_le]
    rintro _ ⟨x, _, r, hr, rfl⟩
    refine ⟨-reducedWedge R L r x, ?_, ?_⟩
    · exact (relationWedges R (quotientMk I)).neg_mem
        (relationWedge_mem R (quotientMk I) ((quotientMk_eq_zero I r).mpr hr) x)
    · rw [map_neg, reducedBracket_wedge]; exact lie_skew x r

theorem bracket_injective_of_homologyTwo_zero
    [Subsingleton (Homology (R := R) (L := L) 2)] :
    Function.Injective (reducedBracket R L) := by
  let e := (secondHomologyConcreteIso R L).toLinearEquiv.trans
    (secondHomologyEquivReducedBracketKernel R L)
  letI : Subsingleton (LinearMap.ker (reducedBracket R L)) := e.symm.injective.subsingleton
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have h := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker
    (reducedBracket R L)) 0)
  exact h

/-- A derived element has a representative in the reduced exterior square. -/
theorem exists_bracket {x : L}
    (hx : x ∈ ⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆) :
    ∃ z, reducedBracket R L z = x := by
  have h : x ∈ (relationWedges R (quotientMk (⊤ : LieIdeal R L))).map
      (reducedBracket R L) := by
    rw [bracket_relationWedges]
    exact hx
  obtain ⟨z, _, hz⟩ := h
  exact ⟨z, hz⟩

end Parafree.Homology.ReducedExterior
