import LieRings.Homological.LieHomology.LowDegree

/-! The incoming differential for third CE homology, with the library's signs. -/
noncomputable section
namespace Parafree.Homology
open LieRings.Homological.LieHomology
variable (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]

theorem differential_three_wedge (x y z w : L) :
    differential R L 3 (exteriorPower.ιMulti R 4 ![x,y,z,w]) =
      -exteriorPower.ιMulti R 3 ![⁅x,y⁆,z,w] -
       exteriorPower.ιMulti R 3 ![y,⁅x,z⁆,w] -
       exteriorPower.ιMulti R 3 ![y,z,⁅x,w⁆] +
       exteriorPower.ιMulti R 3 ![x,⁅y,z⁆,w] +
       exteriorPower.ιMulti R 3 ![x,z,⁅y,w⁆] -
       exteriorPower.ιMulti R 3 ![x,y,⁅z,w⁆] := by
  apply Subtype.ext
  simp only [differential_coe, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_neg,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    Matrix.cons_val_zero, Matrix.tail_cons, Matrix.cons_val_fin_one,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, boundary_ι_mul, adExterior_mul,
    adExterior_ι, boundary_ι, mul_zero, sub_zero, mul_add, mul_sub]
  abel

end Parafree.Homology
