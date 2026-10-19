import Parafree.Associative.FreeWords
import Parafree.Associative.Augmentation

/-! Separatedness of the augmentation filtration on a free associative algebra. -/
noncomputable section
namespace Parafree.Associative.FreeAugmentation
variable (R X : Type*) [CommRing R]

abbrev coordinates : FreeAlgebra R X ≃ₐ[R] MonoidAlgebra R (FreeMonoid X) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid

def orderAtLeast (n : ℕ) : Submodule R (FreeAlgebra R X) where
  carrier := {f | ∀ w : FreeMonoid X, w.toList.length < n → coordinates R X f w = 0}
  zero_mem' := by intro w hw; rw [map_zero]; rfl
  add_mem' := by intro f g hf hg w hw; simp [map_add, hf w hw, hg w hw]
  smul_mem' := by intro c f hf w hw; simp [map_smul, hf w hw]

theorem orderAtLeast_mul {p q : ℕ} {f g : FreeAlgebra R X}
    (hf : f ∈ orderAtLeast R X p) (hg : g ∈ orderAtLeast R X q) :
    f*g ∈ orderAtLeast R X (p+q) := by
  classical
  intro w hw
  by_contra hc
  have hs : w ∈ ((coordinates R X f) * (coordinates R X g)).support := by
    apply Finsupp.mem_support_iff.mpr
    simpa using hc
  obtain ⟨v,hv,u,hu,rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul _ _ hs)
  have hp : p ≤ v.toList.length := by
    by_contra! h
    exact (Finsupp.mem_support_iff.mp hv) (hf v h)
  have hq : q ≤ u.toList.length := by
    by_contra! h
    exact (Finsupp.mem_support_iff.mp hu) (hg u h)
  have he : (v*u).toList.length = v.toList.length + u.toList.length := by
    rw [FreeMonoid.toList_mul, List.length_append]
  omega

theorem coordinates_one_eq_augmentation (f : FreeAlgebra R X) :
    coordinates R X f 1 = FreeAlgebra.algebraMapInv f := by
  have he : (Finsupp.lapply (1 : FreeMonoid X)).comp (coordinates R X).toLinearMap =
      (FreeAlgebra.algebraMapInv : FreeAlgebra R X →ₐ[R] R).toLinearMap := by
    apply (FreeAlgebra.basisFreeMonoid R X).ext
    intro w
    change coordinates R X (word R X w.toList) 1 = FreeAlgebra.algebraMapInv (word R X w.toList)
    rw [word_coordinates, augmentation_word]
    by_cases hw : w.toList = []
    · have he : w = 1 := FreeMonoid.toList.injective hw
      simp [he]
    · have he : w ≠ 1 := by intro he; apply hw; rw [he]; rfl
      simp [hw, Ne.symm he]
  exact LinearMap.congr_fun he f

theorem augmentation_mem_orderAtLeast {f : FreeAlgebra R X}
    (hf : f ∈ augmentationIdeal (FreeAlgebra.algebraMapInv : FreeAlgebra R X →ₐ[R] R)) :
    f ∈ orderAtLeast R X 1 := by
  intro w hw
  have hl : w.toList = [] := List.length_eq_zero_iff.mp (by omega)
  have he : w = 1 := FreeMonoid.toList.injective hl
  rw [he, coordinates_one_eq_augmentation]
  exact hf

theorem power_le_orderAtLeast (n : ℕ) {f : FreeAlgebra R X}
    (hf : f ∈ augmentationIdeal (FreeAlgebra.algebraMapInv : FreeAlgebra R X →ₐ[R] R) ^ n) :
    f ∈ orderAtLeast R X n := by
  induction n generalizing f with
  | zero => intro w hw; omega
  | succ n ih =>
    rw [Submodule.pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      exact orderAtLeast_mul R X (ih ha) (augmentation_mem_orderAtLeast R X hb)
    · intro a b ha hb
      exact (orderAtLeast R X (n+1)).add_mem ha hb

theorem residual_eq_bot :
    augmentationResidual (FreeAlgebra.algebraMapInv : FreeAlgebra R X →ₐ[R] R) = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply (coordinates R X).injective
  ext w
  rw [map_zero]
  have hp := (Submodule.mem_iInf (fun n : ℕ =>
    augmentationIdeal (FreeAlgebra.algebraMapInv : FreeAlgebra R X →ₐ[R] R) ^ n)).mp hf
      (w.toList.length+1)
  exact power_le_orderAtLeast R X _ hp w (by omega)

end Parafree.Associative.FreeAugmentation
