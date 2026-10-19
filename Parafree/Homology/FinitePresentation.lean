import Parafree.Lie.FinitePresentation
import LieRings.Homological.LieHomology.HopfFormula

/-! A finite Lie presentation over a noetherian coefficient ring has finitely
generated actual second Chevalley--Eilenberg homology. -/
noncomputable section
namespace Parafree.Homology.FinitePresentation
open Parafree.Lie LieRings.Homological.LieHomology
variable (R : Type*) [CommRing R] (X : Type*)
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable (p : FreeLieAlgebra R X →ₗ⁅R⁆ L)

def numeratorMap : presentationHopfNumerator R X p →ₗ[R] CentralRelations.image p.ker :=
  LinearMap.codRestrict (CentralRelations.image p.ker)
    ((CentralRelations.project p.ker).toLinearMap.comp
      (presentationHopfNumerator R X p).toSubmodule.subtype)
    (fun x => ⟨x.1,x.2.1,rfl⟩)

theorem numeratorMap_kernel : LinearMap.ker (numeratorMap R X p) =
    presentationHopfRelations R X p := by
  ext x
  change (numeratorMap R X p x = 0) ↔ _
  rw [Subtype.ext_iff]
  change CentralRelations.project p.ker x.1 = 0 ↔ x.1 ∈ CentralRelations.denominator p.ker
  exact CentralRelations.project_zero_iff p.ker x.1

/-- The Hopf multiplier embeds into the module of central relation classes. -/
def hopfInjection : PresentationHopfMultiplier R X p →ₗ[R] CentralRelations.image p.ker :=
  (presentationHopfRelations R X p).liftQ (numeratorMap R X p)
    (by rw [numeratorMap_kernel])

theorem hopfInjection_injective : Function.Injective (hopfInjection R X p) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [numeratorMap_kernel]

variable [IsNoetherianRing R]

theorem homologyTwo_finite_of_finite_relators (hp : Function.Surjective p)
    {ι : Type*} [Finite ι] (r : ι → FreeLieAlgebra R X)
    (hr : p.ker = LieSubmodule.lieSpan R (FreeLieAlgebra R X) (Set.range r)) :
    Module.Finite R (Homology (R := R) (L := L) 2) := by
  letI := CentralRelations.finite_image p.ker r hr
  exact Module.Finite.of_injective
    ((hopfInjection R X p).comp (homologyTwoHopfEquiv R X p hp).toLinearMap)
    ((hopfInjection_injective R X p).comp (homologyTwoHopfEquiv R X p hp).injective)

variable {R X p}

theorem homologyTwo_finite (h : IsFinitelyPresented R L) :
    Module.Finite R (Homology (R := R) (L := L) 2) := by
  obtain ⟨n,p,hp,m,r,hr⟩ := h
  exact homologyTwo_finite_of_finite_relators R (Fin n) p hp r hr

theorem not_finitelyPresented_of_homologyTwo_not_finite
    (h : ¬ Module.Finite R (Homology (R := R) (L := L) 2)) :
    ¬ IsFinitelyPresented R L := fun hp => h (homologyTwo_finite hp)

end Parafree.Homology.FinitePresentation
