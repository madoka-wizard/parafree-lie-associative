import Mathlib.Algebra.Lie.Subalgebra

/-! Descent of a Lie homomorphism through an injective target map, including
restriction to a generated subalgebra. The defining triangle is retained. -/
noncomputable section
namespace Parafree.Lie
variable {R L M N : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
  [LieRing N] [LieAlgebra R N]

namespace InjectiveDescent
variable (i : M →ₗ⁅R⁆ N) (hi : Function.Injective i)
  (f : L →ₗ⁅R⁆ N) (hf : ∀ x, f x ∈ i.range)

def rangeMap : L →ₗ⁅R⁆ i.range where
  toFun x := ⟨f x,hf x⟩
  map_add' x y := Subtype.ext (map_add f x y)
  map_smul' c x := Subtype.ext (map_smul f c x)
  map_lie' {x y} := Subtype.ext (f.map_lie x y)

def hom : L →ₗ⁅R⁆ M :=
  (i.equivRangeOfInjective hi).symm.toLieHom.comp (rangeMap i f hf)

@[simp] theorem triangle (x : L) : i (hom i hi f hf x) = f x := by
  have h := (i.equivRangeOfInjective hi).apply_symm_apply (rangeMap i f hf x)
  exact congrArg Subtype.val h

theorem hom_eq (x : L) (y : M) (h : f x = i y) : hom i hi f hf x = y :=
  hi ((triangle i hi f hf x).trans h)

end InjectiveDescent
end Parafree.Lie
