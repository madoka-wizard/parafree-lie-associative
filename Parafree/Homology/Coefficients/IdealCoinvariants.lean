import Parafree.Associative.IdealCoinvariants
import Parafree.Homology.Coefficients.Coinvariants
import Parafree.Homology.Coefficients.FreeLieIdeal

/-! Zeroth homology of a restricted ambient enveloping algebra, identified
with the enveloping algebra of the actual Lie quotient. -/

noncomputable section

namespace Parafree.Homology.Coefficients.RelativeEnveloping

open LieRings

universe u
variable {R L : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]
  (I : LieIdeal R L)

theorem actionSpan_map :
    (actionSpan R I (Restricted I.incl)).map
      (AssociativeRestriction.equiv (action I.incl) (UEA R L)).toLinearMap =
        Parafree.Associative.IdealCoinvariants.span I := by
  rw [actionSpan, Submodule.map_span, Parafree.Associative.IdealCoinvariants.span]
  congr 1
  ext a
  constructor
  · rintro ⟨m, ⟨x, n, rfl⟩, rfl⟩
    exact ⟨x, AssociativeRestriction.equiv (action I.incl) (UEA R L) n, rfl⟩
  · rintro ⟨x, b, rfl⟩
    let m := (AssociativeRestriction.equiv (action I.incl) (UEA R L)).symm b
    exact ⟨⁅x, m⁆, ⟨x, m, rfl⟩, rfl⟩

def coinvariantsEquiv : Coinvariants R I (Restricted I.incl) ≃ₗ[R] UEA R (L ⧸ I) :=
  (Submodule.Quotient.equiv _ _
    (AssociativeRestriction.equiv (action I.incl) (UEA R L)) (actionSpan_map I)).trans
      (Parafree.Associative.IdealCoinvariants.quotientEquiv I)

/-- Actual categorical zeroth homology, without freeness assumptions. -/
def homologyZeroEquiv : Homology R I (Restricted I.incl) 0 ≃ₗ[R] UEA R (L ⧸ I) :=
  (homologyZeroEquivCoinvariants R I (Restricted I.incl)).trans (coinvariantsEquiv I)

end Parafree.Homology.Coefficients.RelativeEnveloping

namespace Parafree.Homology.Coefficients.FreeAssociative

universe u
variable (R X : Type u) [CommRing R] (J : LieIdeal R (FreeLieAlgebra R X))

def regularHomologyZeroEquiv : Homology R J (Regular (idealAction R X J)) 0 ≃ₗ[R]
    LieRings.UEA R (FreeLieAlgebra R X ⧸ J) :=
  (coefficientHomologyEquiv (restrictedEnvelopingEquiv R X J).symm 0).trans
    (RelativeEnveloping.homologyZeroEquiv J)

end Parafree.Homology.Coefficients.FreeAssociative
