import Parafree.TheoremB.AbelianGeneration
import Parafree.Lie.Parafree
import Parafree.Lie.HomologicalComparison

/-! Parafreeness of the exact rational subring, using its integral embedding.
The composite endomorphism of the free Lie ring is the identity on abelianization;
the lower-central comparison theorem supplies injectivity at every stage. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Parafree.TheoremB

open Parafree.Lie
open LieRings.Homological.LieHomology

def integralEmbedding : P →ₗ⁅ℤ⁆ IntegralFree :=
  integralAlgebra.incl.comp integralEquiv.symm.toLieHom

@[simp] theorem integralEmbedding_generator (i : Fin 4) :
    integralEmbedding (generator i) = integralGenerators i := by
  have he : integralEquiv.symm (generator i) = integralGenerator i := by
    apply integralEquiv.injective
    change integralEquiv (integralEquiv.symm (generator i)) = integralEquiv (integralGenerator i)
    rw [integralEquiv.apply_symm_apply]
    exact (integralToP_generator i).symm
  change (integralEquiv.symm (generator i) : IntegralFree) = _
  rw [he]
  rfl

theorem integralEmbedding_injective : Function.Injective integralEmbedding :=
  Subtype.val_injective.comp integralEquiv.symm.injective

def correctionEndomorphism : IntegralFree →ₗ⁅ℤ⁆ IntegralFree := integralEmbedding.comp freeToP

@[simp] theorem correctionEndomorphism_t : correctionEndomorphism integralT = integralT := by
  change integralEmbedding (freeToP (FreeLieAlgebra.of ℤ 0)) = integralT
  rw [show freeToP (FreeLieAlgebra.of ℤ 0) = t from FreeLieAlgebra.lift_of_apply _ _]
  exact integralEmbedding_generator 0

@[simp] theorem correctionEndomorphism_a :
    correctionEndomorphism integralA = (5 : ℤ) • integralA - (2 : ℤ) • f₁ integralT integralA := by
  change integralEmbedding (freeToP (FreeLieAlgebra.of ℤ 1)) = _
  rw [show freeToP (FreeLieAlgebra.of ℤ 1) = x from FreeLieAlgebra.lift_of_apply _ _]
  change integralEmbedding (a - (2 : ℤ) • u) = _
  rw [map_sub, map_smul]
  rw [show a = generator 1 from rfl, show u = generator 2 from rfl,
    integralEmbedding_generator, integralEmbedding_generator]
  rfl

theorem correctionEndomorphism_abelian : nilpotentMap correctionEndomorphism 1 = LieHom.id := by
  apply quotient_hom_ext
  apply FreeLieAlgebra.hom_ext
  intro i
  change quotientMk _ (correctionEndomorphism (FreeLieAlgebra.of ℤ i)) =
    quotientMk _ (FreeLieAlgebra.of ℤ i)
  have hz (b d : IntegralFree ⧸ lowerCentral ℤ IntegralFree 1) : ⁅b, d⁆ = 0 :=
    lie_eq_zero_of_lowerCentral_one (lowerCentral_quotient_eq_bot 1) b d
  fin_cases i
  · exact congrArg (quotientMk _) correctionEndomorphism_t
  · change quotientMk _ (correctionEndomorphism integralA) = quotientMk _ integralA
    rw [correctionEndomorphism_a, map_sub, map_smul, map_smul, map_f₁]
    simp only [f₁, w, hz, zero_sub, neg_neg]
    module

theorem correctionEndomorphism_isParaEquivalence : IsParaEquivalence correctionEndomorphism := by
  letI : Subsingleton (Homology (R := ℤ) (L := IntegralFree) 2) :=
    homologyTwo_free_subsingleton ℤ (Fin 2)
  apply isParaEquivalence_of_homologyTwo_zero
  rw [correctionEndomorphism_abelian]
  exact Function.bijective_id

theorem freeToP_isParaEquivalence : IsParaEquivalence freeToP := by
  intro n
  refine ⟨?_, nilpotentMap_surjective_of_abelian freeToP abelian_freeToP_surjective n⟩
  have hc : nilpotentMap correctionEndomorphism n =
      (nilpotentMap integralEmbedding n).comp (nilpotentMap freeToP n) := by
    apply quotient_hom_ext
    ext b
    rfl
  intro b d he
  apply (correctionEndomorphism_isParaEquivalence n).1
  simpa only [hc, LieHom.comp_apply] using congrArg (nilpotentMap integralEmbedding n) he

/-- The complete parafreeness assertion, including the specified map of generators. -/
theorem theoremB_part_one : IsParafree P 2 ∧ IsParaEquivalence freeToP :=
  ⟨⟨P_residuallyNilpotent, freeToP, freeToP_isParaEquivalence⟩, freeToP_isParaEquivalence⟩

end Parafree.TheoremB
