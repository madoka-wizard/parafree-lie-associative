import Parafree.Homology.Coefficients.AssociativeRestriction
import Parafree.Homology.Coefficients.DirectSum

/-! Equivariant transport of restricted regular modules and their families. -/

noncomputable section

namespace Parafree.Homology.Coefficients.AssociativeRestriction

open scoped DirectSum

variable {R L A B : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  (f : L →ₗ⁅R⁆ A) (g : L →ₗ⁅R⁆ B)

/-- An algebra equivalence compatible with the acting Lie algebra restricts
 to an equivalence of left regular coefficient modules. -/
def regularCongr (e : A ≃ₐ[R] B) (he : ∀ x, e (f x) = g x) :
    Coefficients f A ≃ₗ⁅R,L⁆ Coefficients g B :=
  { (equiv f A).trans (e.toLinearEquiv.trans (equiv g B).symm) with
    map_lie' := by
      intro x a
      apply (equiv g B).injective
      change e (f x * equiv f A a) = g x * e (equiv f A a)
      rw [map_mul, he] }

variable (X M : Type*) [AddCommGroup M] [Module R M] [Module A M]
  [IsScalarTower R A M] [DecidableEq X]

/-- Restricted finite families are the direct sum of the restricted modules. -/
def finsuppEquiv : Coefficients f (X →₀ M) ≃ₗ⁅R,L⁆ (⨁ _ : X, Coefficients f M) :=
  { (equiv f (X →₀ M)).trans
      ((Finsupp.mapRange.linearEquiv (equiv f M).symm).trans
        (finsuppLEquivDirectSum R (Coefficients f M) X)) with
    map_lie' := by
      intro x a
      ext i
      rfl }

end Parafree.Homology.Coefficients.AssociativeRestriction
