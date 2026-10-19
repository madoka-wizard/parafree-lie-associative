import Parafree.Homology.ScalarReduction

/-! Transport of concrete middle homology along an isomorphism of three-term complexes. -/

noncomputable section

namespace Parafree.Homology.ScalarReduction

variable {R : Type*} [CommRing R]
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
  [AddCommGroup C₃] [Module R C₃] [AddCommGroup D₁] [Module R D₁]
  [AddCommGroup D₂] [Module R D₂] [AddCommGroup D₃] [Module R D₃]
variable (d₂ : C₂ →ₗ[R] C₁) (d₃ : C₃ →ₗ[R] C₂) (h : d₂.comp d₃ = 0)
  (e₂ : D₂ →ₗ[R] D₁) (e₃ : D₃ →ₗ[R] D₂) (k : e₂.comp e₃ = 0)
  (f₁ : C₁ ≃ₗ[R] D₁) (f₂ : C₂ ≃ₗ[R] D₂) (f₃ : C₃ ≃ₗ[R] D₃)
  (h₂ : ∀ x, f₁ (d₂ x) = e₂ (f₂ x)) (h₃ : ∀ x, f₂ (d₃ x) = e₃ (f₃ x))

def cyclesEquiv : d₂.ker ≃ₗ[R] e₂.ker where
  toFun x := ⟨f₂ x.val, by
    change e₂ (f₂ x.val) = 0
    rw [← h₂, x.property, map_zero]⟩
  invFun y := ⟨f₂.symm y.val, by
    apply f₁.injective
    rw [map_zero, h₂, f₂.apply_symm_apply]
    exact y.property⟩
  left_inv _ := Subtype.ext (f₂.symm_apply_apply _)
  right_inv _ := Subtype.ext (f₂.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (map_add f₂ _ _)
  map_smul' _ _ := Subtype.ext (map_smul f₂ _ _)

include h₃ in
theorem cyclesEquiv_boundaries :
    (boundary d₂ d₃ h).range.map (cyclesEquiv d₂ e₂ f₁ f₂ h₂).toLinearMap =
      (boundary e₂ e₃ k).range := by
  ext y
  constructor
  · rintro ⟨x, ⟨b, rfl⟩, rfl⟩
    exact ⟨f₃ b, Subtype.ext (h₃ b).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨boundary d₂ d₃ h (f₃.symm b), ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    change f₂ (d₃ (f₃.symm b)) = e₃ b
    rw [h₃, f₃.apply_symm_apply]

def congrEquiv : Homology d₂ d₃ h ≃ₗ[R] Homology e₂ e₃ k :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv d₂ e₂ f₁ f₂ h₂)
    (cyclesEquiv_boundaries d₂ d₃ h e₂ e₃ k f₁ f₂ f₃ h₂ h₃)

def congrAddEquiv : Homology d₂ d₃ h ≃+ Homology e₂ e₃ k :=
  (congrEquiv d₂ d₃ h e₂ e₃ k f₁ f₂ f₃ h₂ h₃).toAddEquiv

end Parafree.Homology.ScalarReduction
