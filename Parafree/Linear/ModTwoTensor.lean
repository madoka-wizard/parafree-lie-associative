import Parafree.Linear.ModScalar
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing

/-! Tensoring an integral module with the two-element field. -/

noncomputable section

namespace Parafree.Linear.ModScalar

open scoped TensorProduct Pointwise

section General

variable {R : Type*} [CommRing R] (r : R) (M : Type*) [AddCommGroup M] [Module R M]

theorem ideal_smul_top :
    (Ideal.span {r}) • (⊤ : Submodule R M) = multiples r M := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  rfl

def quotTensorAddEquiv : ((R ⧸ Ideal.span {r}) ⊗[R] M) ≃+ Quotient r M :=
  ((TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {r})).trans
    (Submodule.quotEquivOfEq _ _ (ideal_smul_top r M))).toAddEquiv

@[simp] theorem quotTensorAddEquiv_one (x : M) :
    quotTensorAddEquiv r M (1 ⊗ₜ[R] x) = mk r M x := by
  simp [quotTensorAddEquiv, mk]

end General

variable (M : Type*) [AddCommGroup M] [Module ℤ M]

/-- Tensor form of reduction modulo two, with the usual additive structure. -/
def tensorTwoAddEquiv : (ZMod 2 ⊗[ℤ] M) ≃+ Quotient (2 : ℤ) M :=
  ((TensorProduct.congr (Int.quotientSpanNatEquivZMod 2).symm.toAddEquiv.toIntLinearEquiv
      (LinearEquiv.refl ℤ M)).toAddEquiv).trans (quotTensorAddEquiv (2 : ℤ) M)

def tensorTwoEquiv : (ZMod 2 ⊗[ℤ] M) ≃ₗ[ℤ] Quotient (2 : ℤ) M :=
  (tensorTwoAddEquiv M).toIntLinearEquiv

@[simp] theorem tensorTwoEquiv_one (x : M) : tensorTwoEquiv M (1 ⊗ₜ[ℤ] x) = mk (2 : ℤ) M x := by
  change tensorTwoAddEquiv M (1 ⊗ₜ[ℤ] x) = _
  simp [tensorTwoAddEquiv]
  change quotTensorAddEquiv (2 : ℤ) M
    ((Int.quotientSpanNatEquivZMod 2).symm 1 ⊗ₜ[ℤ] x) = _
  rw [map_one, quotTensorAddEquiv_one]

@[simp] theorem tensorTwoEquiv_symm_mk (x : M) :
    (tensorTwoEquiv M).symm (mk (2 : ℤ) M x) = 1 ⊗ₜ[ℤ] x :=
  (tensorTwoEquiv M).symm_apply_eq.mpr (tensorTwoEquiv_one M x).symm

end Parafree.Linear.ModScalar
