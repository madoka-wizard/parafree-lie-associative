import Parafree.Homology.Coefficients.Acyclicity

/-!
# Restricting associative representations to Lie coefficients

The type synonym keeps the left multiplication action distinct from an
associative algebra's adjoint Lie action. An associative-linear map or
equivalence becomes an equivariant coefficient map or equivalence.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.AssociativeRestriction

universe u v w z z'
variable {R : Type u} {L : Type v} {A : Type w}
  [CommRing R] [LieRing L] [LieAlgebra R L] [Ring A] [Algebra R A]
variable (f : L →ₗ⁅R⁆ A) (M : Type z)

def Coefficients (_f : L →ₗ⁅R⁆ A) (M : Type z) := M

instance [AddCommGroup M] : AddCommGroup (Coefficients f M) := inferInstanceAs (AddCommGroup M)
instance [AddCommGroup M] [Module R M] : Module R (Coefficients f M) :=
  inferInstanceAs (Module R M)

def equiv [AddCommGroup M] [Module R M] : Coefficients f M ≃ₗ[R] M := LinearEquiv.refl R M

variable [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

instance : LieRingModule L (Coefficients f M) where
  bracket x m := (equiv f M).symm (f x • equiv f M m)
  add_lie x y m := by
    apply (equiv f M).injective
    change f (x + y) • equiv f M m = f x • equiv f M m + f y • equiv f M m
    rw [map_add, add_smul]
  lie_add x m n := by
    apply (equiv f M).injective
    exact smul_add (f x) (equiv f M m) (equiv f M n)
  leibniz_lie x y m := by
    apply (equiv f M).injective
    change f x • (f y • equiv f M m) =
      f ⁅x,y⁆ • equiv f M m + f y • (f x • equiv f M m)
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, sub_smul, mul_smul, mul_smul]
    abel

instance : LieModule R L (Coefficients f M) where
  smul_lie r x m := by
    apply (equiv f M).injective
    change f (r • x) • equiv f M m = r • (f x • equiv f M m)
    rw [map_smul, smul_assoc]
  lie_smul r x m := by
    apply (equiv f M).injective
    exact smul_algebra_smul_comm r (f x) (equiv f M m)

omit [IsScalarTower R A M] in
@[simp] theorem equiv_lie (x : L) (m : Coefficients f M) :
    equiv f M ⁅x,m⁆ = f x • equiv f M m := rfl

variable {M} {N : Type z'} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- Restrict an associative-linear map to an equivariant Lie coefficient map. -/
def map (g : M →ₗ[A] N) : Coefficients f M →ₗ⁅R,L⁆ Coefficients f N :=
  { (equiv f N).symm.toLinearMap.comp ((g.restrictScalars R).comp (equiv f M).toLinearMap) with
    map_lie' := by
      intro x m
      apply (equiv f N).injective
      exact g.map_smul (f x) (equiv f M m) }

/-- Restrict an associative-linear equivalence, retaining equivariance. -/
def congr (e : M ≃ₗ[A] N) : Coefficients f M ≃ₗ⁅R,L⁆ Coefficients f N :=
  { (equiv f M).trans ((e.restrictScalars R).trans (equiv f N).symm) with
    map_lie' := by
      intro x m
      apply (equiv f N).injective
      exact e.map_smul (f x) (equiv f M m) }

end Parafree.Homology.Coefficients.AssociativeRestriction
