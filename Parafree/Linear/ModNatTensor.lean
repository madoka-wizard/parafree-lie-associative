import Parafree.Linear.ModTwoTensor

/-! Tensor form of reduction modulo an arbitrary natural number. -/

noncomputable section
namespace Parafree.Linear.ModScalar

open scoped TensorProduct
variable (n : ℕ) (M : Type*) [AddCommGroup M] [Module ℤ M]

def tensorNatAddEquiv : (ZMod n ⊗[ℤ] M) ≃+ Quotient (n : ℤ) M :=
  ((TensorProduct.congr (Int.quotientSpanNatEquivZMod n).symm.toAddEquiv.toIntLinearEquiv
      (LinearEquiv.refl ℤ M)).toAddEquiv).trans (quotTensorAddEquiv (n : ℤ) M)

def tensorNatEquiv : (ZMod n ⊗[ℤ] M) ≃ₗ[ℤ] Quotient (n : ℤ) M :=
  (tensorNatAddEquiv n M).toIntLinearEquiv

@[simp] theorem tensorNatEquiv_one (x : M) :
    tensorNatEquiv n M (1 ⊗ₜ[ℤ] x) = mk (n : ℤ) M x := by
  change tensorNatAddEquiv n M (1 ⊗ₜ[ℤ] x) = _
  simp [tensorNatAddEquiv]
  change quotTensorAddEquiv (n : ℤ) M
    ((Int.quotientSpanNatEquivZMod n).symm 1 ⊗ₜ[ℤ] x) = _
  rw [map_one, quotTensorAddEquiv_one]

@[simp] theorem tensorNatEquiv_symm_mk (x : M) :
    (tensorNatEquiv n M).symm (mk (n : ℤ) M x) = 1 ⊗ₜ[ℤ] x :=
  (tensorNatEquiv n M).symm_apply_eq.mpr (tensorNatEquiv_one n M x).symm

end Parafree.Linear.ModScalar
