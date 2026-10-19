import Parafree.TheoremA.PresentationTorsion
import Parafree.TheoremA.ModTwoHomology
import Parafree.TheoremA.AuxiliaryPresentation

/-!
The explicit integral quotient onto the auxiliary algebra and its section modulo two.
`ZeroDegree.lean` and `PositiveFree.lean` identify the kernel in the
graded model used by the completed proof.
-/

noncomputable section

namespace Parafree.TheoremA.AuxiliaryQuotient

open CrossProduct
open scoped TensorProduct

def presentationMap : K →ₗ⁅ℤ⁆ CrossProduct ℤ :=
  K.lift (fun _ => 0) ![z ℤ, u ℤ, v ℤ] (by
    funext i
    fin_cases i <;> simp [equationStep])

private theorem integral_two_injective :
    Function.Injective (fun x : CrossProduct ℤ => (2 : ℤ) • x) := by
  intro a b h
  funext i
  have hi := congrFun h i
  change 2 * a i = 2 * b i at hi
  omega

def integralMap : L →ₗ⁅ℤ⁆ CrossProduct ℤ :=
  K.descend presentationMap integral_two_injective

@[simp] theorem integralMap_x (i : Fin 3) :
    integralMap (toL (K.x i)) = ![z ℤ, u ℤ, v ℤ] i := by
  simp only [integralMap, K.descend_toL, presentationMap, K.lift_x]

@[simp] theorem integralMap_q (i : Fin 3) : integralMap (toL (K.q i)) = 0 := by
  simp only [integralMap, K.descend_toL, presentationMap, K.lift_q]

theorem integralMap_surjective : Function.Surjective integralMap := by
  intro a
  refine ⟨a 0 • toL (K.x 0) + a 1 • toL (K.x 1) + a 2 • toL (K.x 2), ?_⟩
  simp only [map_add, map_smul, integralMap_x, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  exact (coordinates ℤ a).symm

def coefficientMap : CrossProduct ℤ →ₗ⁅ℤ⁆ CrossProduct (ZMod 2) :=
  CrossProduct.lift ℤ (z (ZMod 2)) (u (ZMod 2)) (v (ZMod 2))
    (lie_u_v _) (lie_v_z _) (lie_z_u _)

def modTwoMap : LmodTwo →ₗ⁅ZMod 2⁆ CrossProduct (ZMod 2) :=
  Parafree.Lie.ScalarExtension.lift (ZMod 2) (coefficientMap.comp integralMap)

@[simp] theorem modTwoMap_x (i : Fin 3) :
    modTwoMap ((1 : ZMod 2) ⊗ₜ[ℤ] toL (K.x i)) =
      ![z (ZMod 2), u (ZMod 2), v (ZMod 2)] i := by
  change (1 : ZMod 2) • coefficientMap (integralMap (toL (K.x i))) = _
  rw [one_smul, integralMap_x]
  change (![z ℤ, u ℤ, v ℤ] i) 0 • z (ZMod 2) +
    (![z ℤ, u ℤ, v ℤ] i) 1 • u (ZMod 2) +
    (![z ℤ, u ℤ, v ℤ] i) 2 • v (ZMod 2) = _
  fin_cases i
  · change (1 : ℤ) • z (ZMod 2) + (0 : ℤ) • u (ZMod 2) +
      (0 : ℤ) • v (ZMod 2) = z (ZMod 2)
    simp only [one_smul, zero_smul, add_zero]
  · change (0 : ℤ) • z (ZMod 2) + (1 : ℤ) • u (ZMod 2) +
      (0 : ℤ) • v (ZMod 2) = u (ZMod 2)
    simp only [one_smul, zero_smul, zero_add, add_zero]
  · change (0 : ℤ) • z (ZMod 2) + (0 : ℤ) • u (ZMod 2) +
      (1 : ℤ) • v (ZMod 2) = v (ZMod 2)
    simp only [one_smul, zero_smul, zero_add]

@[simp] theorem modTwoMap_q (i : Fin 3) :
    modTwoMap ((1 : ZMod 2) ⊗ₜ[ℤ] toL (K.q i)) = 0 := by
  change (1 : ZMod 2) • coefficientMap (integralMap (toL (K.q i))) = 0
  rw [integralMap_q, map_zero, smul_zero]

private def reducedPresentation : K →ₗ⁅ℤ⁆ LmodTwo :=
  (Parafree.Homology.ExteriorScalarChange.tensorUnit (ZMod 2)).comp toL

private theorem twice_zero (a : LmodTwo) : (2 : ℤ) • a = 0 := by
  have h : (2 : ℤ) • a = (2 : ZMod 2) • a := by simp only [two_smul]
  rw [h, show (2 : ZMod 2) = 0 by decide, zero_smul]

private theorem reduced_double (a : K) : reducedPresentation (2 • a) = 0 := by
  rw [two_smul, map_add]
  simpa only [two_smul] using twice_zero (reducedPresentation a)

private theorem reduced_relation_z :
    ⁅reducedPresentation (K.x 1), reducedPresentation (K.x 2)⁆ =
      reducedPresentation (K.x 0) := by
  have h := congrArg reducedPresentation K.relation_z
  simpa only [map_add, LieHom.map_lie, reduced_double, add_zero] using h.symm

private theorem reduced_relation_u :
    ⁅reducedPresentation (K.x 2), reducedPresentation (K.x 0)⁆ =
      reducedPresentation (K.x 1) := by
  have h := congrArg reducedPresentation K.relation_u
  simpa only [map_add, LieHom.map_lie, reduced_double, add_zero] using h.symm

private theorem reduced_relation_v :
    ⁅reducedPresentation (K.x 0), reducedPresentation (K.x 1)⁆ =
      -reducedPresentation (K.x 2) := by
  have h := congrArg reducedPresentation K.relation_v
  simp only [map_sub, LieHom.map_lie, reduced_double, zero_sub] at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

def modTwoSection : CrossProduct (ZMod 2) →ₗ⁅ZMod 2⁆ LmodTwo :=
  CrossProduct.lift (ZMod 2)
    (reducedPresentation (K.x 0)) (reducedPresentation (K.x 1))
    (reducedPresentation (K.x 2)) reduced_relation_z reduced_relation_u reduced_relation_v

@[simp] theorem modTwoSection_z :
    modTwoSection (z (ZMod 2)) = (1 : ZMod 2) ⊗ₜ[ℤ] toL (K.x 0) :=
  CrossProduct.lift_z _ _ _ _ _ _ _

@[simp] theorem modTwoSection_u :
    modTwoSection (u (ZMod 2)) = (1 : ZMod 2) ⊗ₜ[ℤ] toL (K.x 1) :=
  CrossProduct.lift_u _ _ _ _ _ _ _

@[simp] theorem modTwoSection_v :
    modTwoSection (v (ZMod 2)) = (1 : ZMod 2) ⊗ₜ[ℤ] toL (K.x 2) :=
  CrossProduct.lift_v _ _ _ _ _ _ _

theorem projection_section : modTwoMap.comp modTwoSection = LieHom.id := by
  apply CrossProduct.hom_ext
  · simp only [LieHom.comp_apply, modTwoSection_z, modTwoMap_x, Matrix.cons_val_zero,
      LieHom.id_apply]
  · simp only [LieHom.comp_apply, modTwoSection_u, modTwoMap_x, Matrix.cons_val_one,
      LieHom.id_apply]
    rfl
  · simp only [LieHom.comp_apply, modTwoSection_v, modTwoMap_x, Matrix.cons_val_two,
      LieHom.id_apply]
    rfl

theorem modTwoMap_surjective : Function.Surjective modTwoMap :=
  (show Function.RightInverse modTwoSection modTwoMap from
    fun a => DFunLike.congr_fun projection_section a).surjective

theorem modTwoSection_injective : Function.Injective modTwoSection :=
  (show Function.LeftInverse modTwoMap modTwoSection from
    fun a => DFunLike.congr_fun projection_section a).injective

end Parafree.TheoremA.AuxiliaryQuotient
