import Mathlib.Algebra.Lie.Basic

/-! Transport of a Lie structure across an existing linear equivalence.
The additive and scalar structures are retained, rather than reconstructed. -/

noncomputable section
namespace Parafree.Lie.Transport

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [LieRing N] [LieAlgebra R N] (e : M ≃ₗ[R] N)

/-- Pull back the bracket along a linear equivalence. -/
@[implicit_reducible] def lieRing : LieRing M where
  toAddCommGroup := inferInstance
  bracket x y := e.symm ⁅e x, e y⁆
  add_lie x y z := by
    change e.symm ⁅e (x + y), e z⁆ = e.symm ⁅e x, e z⁆ + e.symm ⁅e y, e z⁆
    rw [map_add, add_lie, map_add]
  lie_add x y z := by
    change e.symm ⁅e x, e (y + z)⁆ = e.symm ⁅e x, e y⁆ + e.symm ⁅e x, e z⁆
    rw [map_add, lie_add, map_add]
  lie_self x := by
    change e.symm ⁅e x, e x⁆ = 0
    rw [lie_self, map_zero]
  leibniz_lie x y z := by
    change e.symm ⁅e x, e (e.symm ⁅e y, e z⁆)⁆ =
      e.symm ⁅e (e.symm ⁅e x, e y⁆), e z⁆ + e.symm ⁅e y, e (e.symm ⁅e x, e z⁆)⁆
    simp only [LinearEquiv.apply_symm_apply]
    rw [leibniz_lie, map_add]

/-- Compatibility with the existing scalar multiplication. -/
@[implicit_reducible] def lieAlgebra : @LieAlgebra R M _ (lieRing e) := by
  letI := lieRing e
  exact {
    toModule := inferInstance
    lie_smul := fun r x y => by
      change e.symm ⁅e x, e (r • y)⁆ = r • e.symm ⁅e x, e y⁆
      rw [map_smul, lie_smul, map_smul] }

/-- The linear equivalence as an equivalence of the transported Lie structures. -/
def equiv : @LieEquiv R M N _ (lieRing e) (lieAlgebra e) _ _ := by
  letI := lieRing e
  letI := lieAlgebra e
  exact { e with map_lie' := fun {x y} => e.apply_symm_apply ⁅e x, e y⁆ }

end Parafree.Lie.Transport
