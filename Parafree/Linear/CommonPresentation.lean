import Mathlib.LinearAlgebra.Isomorphisms

/-! Canonical comparison of two modules presented by the same generators
and the same kernel. The direct descent avoids nested quotient coercions. -/

noncomputable section
namespace Parafree.Linear

variable {R M N P : Type*} [CommRing R]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

private theorem commonPresentation_map_eq (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (hker : LinearMap.ker f ≤ LinearMap.ker g) {x y : M} (h : f x = f y) : g x = g y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hker
  change f (x - y) = 0
  rw [map_sub, h, sub_self]

/-- Descend a linear map along a surjection when it kills the kernel. -/
def commonPresentationMap (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (hf : Function.Surjective f) (hker : LinearMap.ker f ≤ LinearMap.ker g) : N →ₗ[R] P where
  toFun n := g (hf n).choose
  map_add' a b := by
    rw [← map_add]
    apply commonPresentation_map_eq f g hker
    rw [(hf (a + b)).choose_spec, map_add, (hf a).choose_spec, (hf b).choose_spec]
  map_smul' r a := by
    rw [← map_smul]
    apply commonPresentation_map_eq f g hker
    rw [(hf (r • a)).choose_spec, map_smul, (hf a).choose_spec]
    rfl

@[simp] theorem commonPresentationMap_apply (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (hf : Function.Surjective f) (hker : LinearMap.ker f ≤ LinearMap.ker g) (x : M) :
    commonPresentationMap f g hf hker (f x) = g x :=
  commonPresentation_map_eq f g hker (hf (f x)).choose_spec

/-- Two surjective linear presentations with identical relations define an equivalence. -/
def equivOfCommonPresentation (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : LinearMap.ker f = LinearMap.ker g) : N ≃ₗ[R] P where
  __ := commonPresentationMap f g hf hker.le
  invFun p := f (hg p).choose
  left_inv n := by
    change f (hg (g (hf n).choose)).choose = n
    exact (commonPresentation_map_eq g f hker.ge (hg (g (hf n).choose)).choose_spec).trans
      (hf n).choose_spec
  right_inv p := by
    change commonPresentationMap f g hf hker.le (f (hg p).choose) = p
    rw [commonPresentationMap_apply]
    exact (hg p).choose_spec

@[simp] theorem equivOfCommonPresentation_apply (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : LinearMap.ker f = LinearMap.ker g) (x : M) :
    equivOfCommonPresentation f g hf hg hker (f x) = g x :=
  commonPresentationMap_apply f g hf hker.le x

end Parafree.Linear
