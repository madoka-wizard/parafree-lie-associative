import Parafree.TheoremC.NilpotentInverse

/-! The canonical maps used in Theorem C induce isomorphisms on every
finite augmentation quotient, uniformly over commutative coefficient rings. -/
noncomputable section
namespace Parafree.TheoremC
open Parafree.Associative
variable (k : Type*) [CommRing k]

theorem fourToInitial_isParaEquivalence : (augmentedFourToInitial k).IsParaEquivalence := by
  intro n
  cases n with
  | zero =>
    have hF : augmentationIdeal (fourAugmentation k) ^ 0 = ⊤ := by
      rw [Submodule.pow_zero, Ideal.one_eq_top]
    have hA : initialAugmentationIdeal k ^ 0 = ⊤ := by
      rw [Submodule.pow_zero, Ideal.one_eq_top]
    haveI : Subsingleton (FreeAlgebra k (Fin 4) ⧸ augmentationIdeal (fourAugmentation k) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr hF
    haveI : Subsingleton (A₀ k ⧸ initialAugmentationIdeal k ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr hA
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩
  | succ n => exact NilpotentInverse.forward_bijective k n

def augmentedFourToFull : AugmentedHom (fourAugmentation k) (augmentation k) :=
  (augmentedProjection k).comp (augmentedFourToInitial k)

theorem fourToFull_isParaEquivalence : (augmentedFourToFull k).IsParaEquivalence :=
  AugmentedHom.paraEquivalence_comp _ _ (projection_isParaEquivalence k)
    (fourToInitial_isParaEquivalence k)

/-- The two para-equivalences used to prove Theorem C. -/
theorem canonicalMaps_isParaEquivalence :
    (augmentedFourToInitial k).IsParaEquivalence ∧
    (augmentedProjection k).IsParaEquivalence :=
  ⟨fourToInitial_isParaEquivalence k, projection_isParaEquivalence k⟩

end Parafree.TheoremC
