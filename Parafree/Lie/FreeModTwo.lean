import Parafree.Lie.FreeModNat

/-! Compatibility API for reduction modulo two, specialized from `FreeModNat`. -/

noncomputable section
namespace Parafree.Lie.FreeModTwo

open Parafree.Linear
variable (X : Type*)

def equiv : ModScalar.Quotient (2 : ℤ) (FreeLieAlgebra ℤ X) ≃ₗ[ℤ]
    FreeLieAlgebra (ZMod 2) X := FreeModNat.equiv 2 X

theorem equiv_mk (x : FreeLieAlgebra ℤ X) :
    equiv X (ModScalar.mk (2 : ℤ) _ x) = FreeScalarExtension.generatorMap (ZMod 2) X x :=
  FreeModNat.equiv_mk 2 X x

theorem generatorMap_surjective :
    Function.Surjective (FreeScalarExtension.generatorMap (ZMod 2) X) :=
  FreeModNat.generatorMap_surjective 2 X

theorem generatorMap_eq_zero_iff (x : FreeLieAlgebra ℤ X) :
    FreeScalarExtension.generatorMap (ZMod 2) X x = 0 ↔
      ∃ y : FreeLieAlgebra ℤ X, (2 : ℤ) • y = x :=
  FreeModNat.generatorMap_eq_zero_iff 2 X x

end Parafree.Lie.FreeModTwo
