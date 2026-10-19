import Parafree.TheoremB.AuxiliaryCoefficients
import Parafree.Lie.FreeScalarExtension

/-! The exact auxiliary presentation commutes with scalar extension from
integers. This also identifies its localization, rather than merely comparing
an abstract isomorphic solvable model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB.Auxiliary
open Parafree.Lie
open scoped TensorProduct

section Universal
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

def lift (x y : L) (h₁ : f₁ x y = 0) (h₂ : f₂ x y = 0) : Presented R →ₗ⁅R⁆ L :=
  quotientLift (relationIdeal R) (FreeLieAlgebra.lift R ![x,y]) (by
    apply LieSubmodule.lieSpan_le.mpr
    rintro _ ⟨i,rfl⟩
    change FreeLieAlgebra.lift R ![x,y] (relator R i) = 0
    fin_cases i
    · change FreeLieAlgebra.lift R ![x,y] (f₁ (generator R 0) (generator R 1)) = 0
      simpa only [f₁,w,map_sub,LieHom.map_lie,map_zsmul,generator,
        FreeLieAlgebra.lift_of_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using h₁
    · change FreeLieAlgebra.lift R ![x,y] (f₂ (generator R 0) (generator R 1)) = 0
      simpa only [f₂,h,c,w,map_sub,LieHom.map_lie,map_zsmul,generator,
        FreeLieAlgebra.lift_of_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using h₂)

@[simp] theorem lift_gen (x y : L) (h₁ : f₁ x y = 0) (h₂ : f₂ x y = 0) (i : Fin 2) :
    lift x y h₁ h₂ (gen R i) = ![x,y] i := FreeLieAlgebra.lift_of_apply _ _

theorem hom_ext {f g : Presented R →ₗ⁅R⁆ L} (hfg : ∀ i, f (gen R i) = g (gen R i)) : f = g := by
  apply quotient_hom_ext
  apply FreeLieAlgebra.hom_ext
  exact hfg
end Universal

variable (S : Type*) [CommRing S]

def integralMap : Presented ℤ →ₗ⁅ℤ⁆ Presented S :=
  lift (gen S 0) (gen S 1) (presented_f₁ S) (presented_f₂ S)

@[simp] theorem integralMap_gen (i : Fin 2) : integralMap S (gen ℤ i) = gen S i := by
  rw [integralMap,lift_gen]
  fin_cases i <;> rfl

def scalarForward : (S ⊗[ℤ] Presented ℤ) →ₗ⁅S⁆ Presented S := ScalarExtension.lift S (integralMap S)

def scalarBackward : Presented S →ₗ⁅S⁆ (S ⊗[ℤ] Presented ℤ) :=
  lift (FreeScalarExtension.unit S (gen ℤ 0)) (FreeScalarExtension.unit S (gen ℤ 1))
    (by rw [← map_f₁,presented_f₁,map_zero])
    (by rw [← map_f₂,presented_f₂,map_zero])

@[simp] theorem scalarForward_one (x : Presented ℤ) : scalarForward S (1 ⊗ₜ[ℤ] x) = integralMap S x := by
  change (1:S) • integralMap S x = _
  exact one_smul _ _

@[simp] theorem scalarBackward_gen (i : Fin 2) : scalarBackward S (gen S i) = 1 ⊗ₜ[ℤ] gen ℤ i := by
  rw [scalarBackward,lift_gen]
  fin_cases i <;> rfl

theorem scalarForward_backward : (scalarForward S).comp (scalarBackward S) = LieHom.id := by
  apply hom_ext
  intro i
  change scalarForward S (scalarBackward S (gen S i)) = gen S i
  rw [scalarBackward_gen,scalarForward_one,integralMap_gen]

theorem scalarBackward_integralMap (x : Presented ℤ) :
    scalarBackward S (integralMap S x) = 1 ⊗ₜ[ℤ] x := by
  let f : Presented S →ₗ⁅ℤ⁆ (S ⊗[ℤ] Presented ℤ) :=
    { (scalarBackward S).toLinearMap.restrictScalars ℤ with map_lie' := (scalarBackward S).map_lie _ _ }
  have he : f.comp (integralMap S) = FreeScalarExtension.unit S := by
    apply hom_ext
    intro i
    change scalarBackward S (integralMap S (gen ℤ i)) = 1 ⊗ₜ[ℤ] gen ℤ i
    rw [integralMap_gen,scalarBackward_gen]
  exact LieHom.congr_fun he x

theorem scalarBackward_forward (x : S ⊗[ℤ] Presented ℤ) : scalarBackward S (scalarForward S x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul s x =>
    change scalarBackward S (s • integralMap S x) = _
    rw [map_smul,scalarBackward_integralMap,TensorProduct.smul_tmul',smul_eq_mul,mul_one]

def scalarEquiv : (S ⊗[ℤ] Presented ℤ) ≃ₗ⁅S⁆ Presented S :=
  LieEquiv.ofBijective (scalarForward S)
    ⟨Function.LeftInverse.injective (scalarBackward_forward S),
      Function.RightInverse.surjective (fun x => LieHom.congr_fun (scalarForward_backward S) x)⟩

end Parafree.TheoremB.Auxiliary
