import Mathlib.Algebra.Lie.Quotient

/-! Lie algebra quotient maps and their universal property. -/

namespace Parafree.Lie

variable {R : Type*} [CommRing R]
variable {L M N : Type*} [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N]

def quotientMk (I : LieIdeal R L) : L →ₗ⁅R⁆ L ⧸ I :=
  { I.toSubmodule.mkQ with map_lie' := rfl }

@[simp] theorem quotientMk_eq_zero (I : LieIdeal R L) (x : L) :
    quotientMk I x = 0 ↔ x ∈ I := Submodule.Quotient.mk_eq_zero I.toSubmodule

theorem quotientMk_surjective (I : LieIdeal R L) : Function.Surjective (quotientMk I) :=
  Submodule.mkQ_surjective _

@[simp] theorem quotientMk_ker (I : LieIdeal R L) : (quotientMk I).ker = I := by
  ext x
  exact quotientMk_eq_zero I x

def quotientLift (I : LieIdeal R L) (f : L →ₗ⁅R⁆ M) (h : I ≤ f.ker) :
    L ⧸ I →ₗ⁅R⁆ M :=
  { I.toSubmodule.liftQ f.toLinearMap h with
    map_lie' := by
      intro x y
      obtain ⟨x, rfl⟩ := quotientMk_surjective I x
      obtain ⟨y, rfl⟩ := quotientMk_surjective I y
      exact f.map_lie x y }

@[simp] theorem quotientLift_mk (I : LieIdeal R L) (f : L →ₗ⁅R⁆ M)
    (h : I ≤ f.ker) (x : L) : quotientLift I f h (quotientMk I x) = f x := rfl

theorem quotient_hom_ext (I : LieIdeal R L) {f g : L ⧸ I →ₗ⁅R⁆ M}
    (h : f.comp (quotientMk I) = g.comp (quotientMk I)) : f = g := by
  apply LieHom.ext
  intro x
  obtain ⟨x, rfl⟩ := quotientMk_surjective I x
  exact DFunLike.congr_fun h x

def quotientMap (I : LieIdeal R L) (J : LieIdeal R M) (f : L →ₗ⁅R⁆ M)
    (h : ∀ x ∈ I, f x ∈ J) : L ⧸ I →ₗ⁅R⁆ M ⧸ J :=
  quotientLift I ((quotientMk J).comp f) (by
    intro x hx
    exact (quotientMk_eq_zero J (f x)).mpr (h x hx))

@[simp] theorem quotientMap_mk (I : LieIdeal R L) (J : LieIdeal R M)
    (f : L →ₗ⁅R⁆ M) (h : ∀ x ∈ I, f x ∈ J) (x : L) :
    quotientMap I J f h (quotientMk I x) = quotientMk J (f x) := rfl

end Parafree.Lie
