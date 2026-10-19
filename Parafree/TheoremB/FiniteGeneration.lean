import Parafree.TheoremB.Model

/-! A surjection from the free integral Lie ring on four generators gives
finite generation of the exact rational subring in the manuscript. -/

noncomputable section
namespace Parafree.TheoremB

/-- The four named elements generate the subring intrinsically as well. -/
theorem generators_lieSpan : LieSubalgebra.lieSpan ℤ P (Set.range generator) = ⊤ := by
  rw [← LieSubalgebra.comap_lieSpan_range_eq ℤ algebra generator]
  apply top_unique
  intro z _
  exact z.property

def generatingMap : FreeLieAlgebra ℤ (Fin 4) →ₗ⁅ℤ⁆ P := FreeLieAlgebra.lift ℤ generator

@[simp] theorem generatingMap_of (i : Fin 4) :
    generatingMap (FreeLieAlgebra.of ℤ i) = generator i := FreeLieAlgebra.lift_of_apply _ _

theorem generatingMap_surjective : Function.Surjective generatingMap := by
  have hr : LieSubalgebra.lieSpan ℤ P (Set.range generator) ≤ generatingMap.range := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨FreeLieAlgebra.of ℤ i, generatingMap_of i⟩
  rw [generators_lieSpan] at hr
  intro z
  exact hr (LieSubalgebra.mem_top z)

end Parafree.TheoremB
