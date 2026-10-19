import Parafree.TheoremA.IntegralModel
import Parafree.Lie.ScalarExtension
import Parafree.Homology.ExteriorScalarChange

/-! An explicit free model after extending scalars to a ring in which two is invertible. -/

noncomputable section

namespace Parafree.TheoremA

open Parafree.Lie
open scoped TensorProduct

theorem K.hom_ext_of_two_smul_injective {M : Type*} [LieRing M]
    (h₂ : Function.Injective (fun x : M => (2 : ℤ) • x))
    {f g : K →ₗ⁅ℤ⁆ M} (hx : ∀ i, f (K.x i) = g (K.x i)) : f = g := by
  apply K.hom_ext hx
  intro i
  apply h₂
  have hx' : (fun j => f (K.x j)) = (fun j => g (K.x j)) := funext hx
  have he : equationStep (fun j => f (K.q j)) (fun j => g (K.x j)) =
      equationStep (fun j => g (K.q j)) (fun j => g (K.x j)) := by
    rw [← hx', K.map_equations, hx', K.map_equations]
  fin_cases i
  · simpa [equationStep, two_smul] using congrFun he 0
  · simpa [equationStep, two_smul] using congrFun he 1
  · simpa [equationStep, two_smul] using congrFun he 2

namespace ScalarModel

variable (S : Type*) [CommRing S]

abbrev Extended := S ⊗[ℤ] L
abbrev Free := FreeLieAlgebra S (Fin 3)

def toFreeIntegral : L →ₗ⁅ℤ⁆ Free S :=
  (FreeLieAlgebra.lift ℤ (FreeLieAlgebra.of S)).comp integralRealization

@[simp] theorem toFreeIntegral_x (i : Fin 3) :
    toFreeIntegral S (toL (K.x i)) = (2 : S) • FreeLieAlgebra.of S i := by
  change FreeLieAlgebra.lift ℤ (FreeLieAlgebra.of S) (integralEvaluation (K.x i)) = _
  rw [integralEvaluation_x, integralX, map_smul, FreeLieAlgebra.lift_of_apply]
  simp only [two_smul]

def toFree : Extended S →ₗ⁅S⁆ Free S :=
  ScalarExtension.lift S (toFreeIntegral S)

@[simp] theorem toFree_tmul (s : S) (x : L) :
    toFree S (s ⊗ₜ[ℤ] x) = s • toFreeIntegral S x := rfl

def fromFree (b : S) : Free S →ₗ⁅S⁆ Extended S :=
  FreeLieAlgebra.lift S (fun i => b • ((1 : S) ⊗ₜ[ℤ] toL (K.x i)))

@[simp] theorem fromFree_of (b : S) (i : Fin 3) :
    fromFree S b (FreeLieAlgebra.of S i) = b • ((1 : S) ⊗ₜ[ℤ] toL (K.x i)) :=
  FreeLieAlgebra.lift_of_apply _ _

variable (b : S) (hb : (2 : S) * b = 1)

include hb in
theorem toFree_fromFree : (toFree S).comp (fromFree S b) = LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro i
  simp only [LieHom.comp_apply, fromFree_of, map_smul, toFree_tmul,
    toFreeIntegral_x, smul_smul, one_mul, mul_comm b 2, hb, one_smul, LieHom.id_apply]

include hb in
theorem two_smul_injective :
    Function.Injective (fun x : Extended S => (2 : ℤ) • x) :=
  ScalarExtension.int_two_smul_injective S b hb _

def fromFreeIntegral : Free S →ₗ⁅ℤ⁆ Extended S where
  __ := (fromFree S b).toLinearMap.restrictScalars ℤ
  map_lie' := (fromFree S b).map_lie _ _

include hb in
theorem fromFree_toFreeIntegral (x : L) :
    fromFree S b (toFreeIntegral S x) = (1 : S) ⊗ₜ[ℤ] x := by
  have hk : ((fromFreeIntegral S b).comp (toFreeIntegral S)).comp toL =
      (Parafree.Homology.ExteriorScalarChange.tensorUnit S).comp toL := by
    apply K.hom_ext_of_two_smul_injective (two_smul_injective S b hb)
    intro i
    change fromFree S b (toFreeIntegral S (toL (K.x i))) = (1 : S) ⊗ₜ[ℤ] toL (K.x i)
    rw [toFreeIntegral_x, map_smul, fromFree_of, smul_smul, hb, one_smul]
  obtain ⟨y, rfl⟩ := quotientMk_surjective (residualIdeal ℤ K) x
  exact DFunLike.congr_fun hk y

include hb in
theorem fromFree_toFree (x : Extended S) : fromFree S b (toFree S x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
    rw [toFree_tmul, map_smul, fromFree_toFreeIntegral S b hb,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The six-generator residual quotient becomes free after two is inverted. -/
def equivFree : Extended S ≃ₗ⁅S⁆ Free S :=
  LieEquiv.ofBijective (toFree S) ⟨
    Function.LeftInverse.injective (fromFree_toFree S b hb),
    Function.RightInverse.surjective (fun x => DFunLike.congr_fun (toFree_fromFree S b hb) x)⟩

end ScalarModel
end Parafree.TheoremA
