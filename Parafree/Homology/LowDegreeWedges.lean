import Parafree.Linear.ExteriorBaseChange
import Mathlib.Algebra.Lie.BaseChange
import LieRings.Homological.LieHomology.LowDegree

/-! Compatibility of exterior scalar change with the CE differentials determining H₂. -/

noncomputable section

namespace Parafree.Homology.ExteriorScalarChange

open LieRings.Homological.LieHomology
open Parafree.Linear.ExteriorBaseChange
open scoped TensorProduct Parafree.Linear.ExteriorBaseChange

variable {R : Type*} [CommRing R] {L : Type*} [LieRing L] [LieAlgebra R L]

theorem differential_one_wedge (x y : L) :
    differential R L 1 (exteriorPower.ιMulti R 2 ![x, y]) =
      -exteriorPower.ιMulti R 1 ![⁅x, y⁆] := by
  apply (exteriorPower.oneEquiv R L).injective
  exact (degreeTwoBoundary_ιMulti R L x y).trans
    (((exteriorPower.oneEquiv R L).map_neg (exteriorPower.ιMulti R 1 ![⁅x, y⁆])).trans
      (congrArg Neg.neg (exteriorPower.oneEquiv_ιMulti (R := R) ![⁅x, y⁆]))).symm

theorem differential_two_wedge (x y z : L) :
    differential R L 2 (exteriorPower.ιMulti R 3 ![x, y, z]) =
      -exteriorPower.ιMulti R 2 ![⁅x, y⁆, z] +
        exteriorPower.ιMulti R 2 ![⁅x, z⁆, y] -
          exteriorPower.ιMulti R 2 ![⁅y, z⁆, x] := by
  apply Subtype.ext
  simpa only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_neg,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.tail_cons, Matrix.cons_val_fin_one,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one] using differential_two_ιMulti_coe R L x y z

end Parafree.Homology.ExteriorScalarChange
