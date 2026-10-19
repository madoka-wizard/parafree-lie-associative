import Mathlib.Algebra.Lie.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The signed rank-three Lie algebra in Theorem A

This is a distinct type: the third coordinate has the opposite sign to the usual cross
product. In particular no Lie structure from the pointwise associative ring is inherited.
-/

namespace Parafree.TheoremA

/-- Coordinates are ordered as `z, u, v`. -/
def CrossProduct (R : Type*) := Fin 3 → R

namespace CrossProduct

variable (R : Type*) [CommRing R]

instance : AddCommGroup (CrossProduct R) := inferInstanceAs (AddCommGroup (Fin 3 → R))
instance : Module R (CrossProduct R) := inferInstanceAs (Module R (Fin 3 → R))

@[simp] theorem zero_apply (i : Fin 3) : (0 : CrossProduct R) i = 0 := rfl
@[simp] theorem add_apply (x y : CrossProduct R) (i : Fin 3) :
    (x + y) i = x i + y i := rfl
@[simp] theorem neg_apply (x : CrossProduct R) (i : Fin 3) : (-x) i = -x i := rfl
@[simp] theorem smul_apply (r : R) (x : CrossProduct R) (i : Fin 3) :
    (r • x) i = r * x i := rfl

instance : Bracket (CrossProduct R) (CrossProduct R) where
  bracket x y := ![x 1 * y 2 - x 2 * y 1,
    x 2 * y 0 - x 0 * y 2, x 1 * y 0 - x 0 * y 1]

theorem bracket_apply (x y : CrossProduct R) :
    ⁅x, y⁆ = ![x 1 * y 2 - x 2 * y 1,
      x 2 * y 0 - x 0 * y 2, x 1 * y 0 - x 0 * y 1] := rfl

instance : LieRing (CrossProduct R) where
  add_lie x y z := by
    funext i
    fin_cases i <;> simp [bracket_apply] <;> ring
  lie_add x y z := by
    funext i
    fin_cases i <;> simp [bracket_apply] <;> ring
  lie_self x := by
    funext i
    fin_cases i <;> simp [bracket_apply] <;> ring
  leibniz_lie x y z := by
    funext i
    fin_cases i <;> simp [bracket_apply] <;> ring

instance : LieAlgebra R (CrossProduct R) where
  lie_smul r x y := by
    funext i
    fin_cases i <;> simp [bracket_apply] <;> ring

def z : CrossProduct R := ![1, 0, 0]
def u : CrossProduct R := ![0, 1, 0]
def v : CrossProduct R := ![0, 0, 1]

@[simp] theorem lie_u_v : ⁅u R, v R⁆ = z R := by
  funext i
  fin_cases i <;> simp [bracket_apply, u, v, z]

@[simp] theorem lie_v_z : ⁅v R, z R⁆ = u R := by
  funext i
  fin_cases i <;> simp [bracket_apply, u, v, z]

@[simp] theorem lie_z_u : ⁅z R, u R⁆ = -v R := by
  funext i
  fin_cases i <;> simp [bracket_apply, u, v, z]

theorem coordinates (x : CrossProduct R) :
    x = x 0 • z R + x 1 • u R + x 2 • v R := by
  funext i
  fin_cases i <;> simp [z, u, v]

end CrossProduct
end Parafree.TheoremA
