import Mathlib.LinearAlgebra.Isomorphisms

/-! Reduction of a module and a linear map modulo a scalar. -/

noncomputable section

namespace Parafree.Linear.ModScalar

variable {R : Type*} [CommRing R]
variable (r : R) (M : Type*) [AddCommGroup M] [Module R M]

def multiples : Submodule R M := LinearMap.range (r • LinearMap.id : M →ₗ[R] M)

abbrev Quotient := M ⧸ multiples r M

def mk : M →ₗ[R] Quotient r M := (multiples r M).mkQ

theorem mk_surjective : Function.Surjective (mk r M) := Submodule.mkQ_surjective _

theorem mk_eq_zero (x : M) : mk r M x = 0 ↔ ∃ y : M, r • y = x :=
  Submodule.Quotient.mk_eq_zero _

@[simp] theorem mk_smul_self (x : M) : mk r M (r • x) = 0 :=
  (mk_eq_zero r M _).mpr ⟨x, rfl⟩

@[simp] theorem smul_quotient (x : Quotient r M) : r • x = 0 := by
  obtain ⟨x, rfl⟩ := mk_surjective r M x
  rw [← map_smul, mk_smul_self]

variable {M} {N : Type*} [AddCommGroup N] [Module R N]

def map (f : M →ₗ[R] N) : Quotient r M →ₗ[R] Quotient r N :=
  (multiples r M).mapQ (multiples r N) f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, (map_smul f r x).symm⟩)

@[simp] theorem map_mk (f : M →ₗ[R] N) (x : M) :
    map r f (mk r M x) = mk r N (f x) := rfl

def congr (e : M ≃ₗ[R] N) : Quotient r M ≃ₗ[R] Quotient r N where
  __ := map r e.toLinearMap
  invFun := map r e.symm.toLinearMap
  left_inv x := by
    obtain ⟨x, rfl⟩ := mk_surjective r M x
    simp
  right_inv x := by
    obtain ⟨x, rfl⟩ := mk_surjective r N x
    simp

/-- The additive comparison avoids choosing an integral module instance on a quotient. -/
def congrAdd (e : M ≃ₗ[R] N) : Quotient r M ≃+ Quotient r N := (congr r e).toAddEquiv

end Parafree.Linear.ModScalar
