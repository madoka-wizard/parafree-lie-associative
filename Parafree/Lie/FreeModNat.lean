import Parafree.Lie.FreeScalarExtension
import Parafree.Linear.ModNatTensor

/-! The free Lie algebra over any quotient ring of integers is the actual reduction
of the integral free Lie algebra, with generator-map kernel and surjectivity. -/

noncomputable section
namespace Parafree.Lie.FreeModNat

open Parafree.Linear
open scoped TensorProduct
variable (n : ℕ) (X : Type*)

def equiv : ModScalar.Quotient (n : ℤ) (FreeLieAlgebra ℤ X) ≃ₗ[ℤ]
    FreeLieAlgebra (ZMod n) X :=
  (ModScalar.tensorNatEquiv n (FreeLieAlgebra ℤ X)).symm.trans
    ((FreeScalarExtension.equiv (ZMod n) X).toLinearEquiv.restrictScalars ℤ)

theorem equiv_mk (x : FreeLieAlgebra ℤ X) :
    equiv n X (ModScalar.mk (n : ℤ) _ x) = FreeScalarExtension.generatorMap (ZMod n) X x := by
  change FreeScalarExtension.equiv (ZMod n) X
    ((ModScalar.tensorNatEquiv n (FreeLieAlgebra ℤ X)).symm (ModScalar.mk (n : ℤ) _ x)) = _
  rw [ModScalar.tensorNatEquiv_symm_mk]
  change (1 : ZMod n) • FreeScalarExtension.generatorMap (ZMod n) X x = _
  exact one_smul _ _

theorem generatorMap_surjective :
    Function.Surjective (FreeScalarExtension.generatorMap (ZMod n) X) := by
  intro x
  obtain ⟨a, rfl⟩ := (equiv n X).surjective x
  obtain ⟨b, rfl⟩ := ModScalar.mk_surjective (n : ℤ) _ a
  exact ⟨b, (equiv_mk n X b).symm⟩

theorem generatorMap_eq_zero_iff (x : FreeLieAlgebra ℤ X) :
    FreeScalarExtension.generatorMap (ZMod n) X x = 0 ↔
      ∃ y : FreeLieAlgebra ℤ X, (n : ℤ) • y = x := by
  rw [← equiv_mk, ← map_zero (equiv n X), (equiv n X).injective.eq_iff]
  exact ModScalar.mk_eq_zero (n : ℤ) _ x

end Parafree.Lie.FreeModNat
