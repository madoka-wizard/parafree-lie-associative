import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Basis.Prod

/-! The split extension of a Lie algebra by an abelian module. This small
coordinate model exposes the crossed-derivation identity used by Fox maps. -/
noncomputable section
namespace Parafree.Lie

@[ext] structure ModuleExtension (G V : Type*) where
  base : G
  coefficient : V

namespace ModuleExtension
variable (R G V : Type*) [CommRing R] [LieRing G] [LieAlgebra R G]
  [AddCommGroup V] [Module R V] [LieRingModule G V] [LieModule R G V]

def coordinates : ModuleExtension G V ≃ G × V where
  toFun x := (x.base,x.coefficient)
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (ModuleExtension G V) := (coordinates G V).addCommGroup
instance : Module R (ModuleExtension G V) := (coordinates G V).module R

def coordinatesLinear : ModuleExtension G V ≃ₗ[R] G × V where
  __ := coordinates G V
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance [Module.Free R G] [Module.Free R V] : Module.Free R (ModuleExtension G V) :=
  Module.Free.of_equiv (coordinatesLinear R G V).symm

instance : Bracket (ModuleExtension G V) (ModuleExtension G V) where
  bracket x y := ⟨⁅x.base,y.base⁆,⁅x.base,y.coefficient⁆ - ⁅y.base,x.coefficient⁆⟩

omit [LieRingModule G V] in
@[simp] theorem base_zero : (0 : ModuleExtension G V).base = 0 := rfl
omit [LieRingModule G V] in
@[simp] theorem coefficient_zero : (0 : ModuleExtension G V).coefficient = 0 := rfl
omit [LieRingModule G V] in
@[simp] theorem base_add (x y : ModuleExtension G V) : (x+y).base = x.base+y.base := rfl
omit [LieRingModule G V] in
@[simp] theorem coefficient_add (x y : ModuleExtension G V) : (x+y).coefficient = x.coefficient+y.coefficient := rfl
omit [LieRingModule G V] [LieModule R G V] in
@[simp] theorem base_smul (r : R) (x : ModuleExtension G V) : (r•x).base = r•x.base := rfl
omit [LieRingModule G V] [LieModule R G V] in
@[simp] theorem coefficient_smul (r : R) (x : ModuleExtension G V) : (r•x).coefficient = r•x.coefficient := rfl
@[simp] theorem base_lie (x y : ModuleExtension G V) : ⁅x,y⁆.base = ⁅x.base,y.base⁆ := rfl
@[simp] theorem coefficient_lie (x y : ModuleExtension G V) :
    ⁅x,y⁆.coefficient = ⁅x.base,y.coefficient⁆ - ⁅y.base,x.coefficient⁆ := rfl

instance : LieRing (ModuleExtension G V) where
  add_lie x y z := by ext <;> simp [add_lie,lie_add]; abel
  lie_add x y z := by ext <;> simp [add_lie,lie_add]; abel
  lie_self x := by ext <;> simp
  leibniz_lie x y z := by
    ext
    · exact leibniz_lie _ _ _
    · simp only [coefficient_lie,base_lie,coefficient_add,lie_sub]
      rw [lie_lie,lie_lie,lie_lie]
      abel

instance : LieAlgebra R (ModuleExtension G V) where
  lie_smul r x y := by ext <;> simp [lie_smul,smul_lie,smul_sub]

def projection : ModuleExtension G V →ₗ⁅R⁆ G where
  toFun x := x.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

def coefficientMap : ModuleExtension G V →ₗ[R] V where
  toFun x := x.coefficient
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def inclusion : G →ₗ⁅R⁆ ModuleExtension G V where
  toFun x := ⟨x,0⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  map_lie' {x y} := by ext <;> simp

def coefficientInclusion : V →ₗ[R] ModuleExtension G V where
  toFun x := ⟨0,x⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def scale (c : R) : ModuleExtension G V →ₗ⁅R⁆ ModuleExtension G V where
  toFun x := ⟨x.base,c•x.coefficient⟩
  map_add' _ _ := by ext <;> simp [smul_add]
  map_smul' r x := by
    apply ModuleExtension.ext
    · rfl
    · exact smul_comm c r x.coefficient
  map_lie' {x y} := by ext <;> simp [smul_sub,lie_smul]

end ModuleExtension
end Parafree.Lie
