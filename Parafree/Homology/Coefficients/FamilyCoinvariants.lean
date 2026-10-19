import Parafree.Linear.FinsuppQuotient
import Parafree.Homology.Coefficients.Coinvariants
import Parafree.Homology.Coefficients.AssociativeRestriction

/-! Coinvariants of finite families of a restricted associative module. -/

noncomputable section

namespace Parafree.Homology.Coefficients.AssociativeRestriction

variable {R L A : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)
  (X M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

def familyLinear : Coefficients f (X →₀ M) ≃ₗ[R] (X →₀ Coefficients f M) :=
  (equiv f (X →₀ M)).trans (Finsupp.mapRange.linearEquiv (equiv f M).symm)

omit [IsScalarTower R A M] in
@[simp] theorem familyLinear_lie_apply (x : L) (m : Coefficients f (X →₀ M)) (i : X) :
    familyLinear f X M ⁅x, m⁆ i = ⁅x, familyLinear f X M m i⁆ := rfl

omit [IsScalarTower R A M] in
theorem actionSpan_family :
    (actionSpan R L (Coefficients f (X →₀ M))).map (familyLinear f X M).toLinearMap =
      Finsupp.submodule (fun _ : X => actionSpan R L (Coefficients f M)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    intro i
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨x, a, rfl⟩ := hm
      exact Submodule.subset_span ⟨x, familyLinear f X M a i, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using (actionSpan R L (Coefficients f M)).add_mem ha hb
    | smul r a _ ha => simpa using (actionSpan R L (Coefficients f M)).smul_mem r ha
  · intro m hm
    have hs (i : X) (a : Coefficients f M) (ha : a ∈ actionSpan R L (Coefficients f M)) :
        Finsupp.single i a ∈
          (actionSpan R L (Coefficients f (X →₀ M))).map (familyLinear f X M).toLinearMap := by
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨x, a, rfl⟩ := ha
        let m := (familyLinear f X M).symm (Finsupp.single i a)
        refine ⟨⁅x, m⁆, Submodule.subset_span ⟨x, m, rfl⟩, ?_⟩
        ext j
        change familyLinear f X M ⁅x, m⁆ j = Finsupp.single i ⁅x, a⁆ j
        rw [familyLinear_lie_apply]
        change ⁅x, familyLinear f X M ((familyLinear f X M).symm (Finsupp.single i a)) j⁆ = _
        rw [LinearEquiv.apply_symm_apply]
        by_cases hij : i = j
        · subst j; simp
        · simp [hij]
      | zero => simp
      | add a b _ _ ha hb => simpa only [Finsupp.single_add] using Submodule.add_mem _ ha hb
      | smul r a _ ha => simpa only [Finsupp.smul_single] using Submodule.smul_mem _ r ha
    rw [← Finsupp.sum_single m]
    exact Submodule.sum_mem _ (fun i _ => hs i (m i) (hm i))

/-- Concrete coinvariants commute with finitely supported families. -/
def familyCoinvariantsEquiv : Coinvariants R L (Coefficients f (X →₀ M)) ≃ₗ[R]
    (X →₀ Coinvariants R L (Coefficients f M)) :=
  (Submodule.Quotient.equiv _ _ (familyLinear f X M) (actionSpan_family f X M)).trans
    (Parafree.Linear.FinsuppQuotient.equiv X (actionSpan R L (Coefficients f M)))

end Parafree.Homology.Coefficients.AssociativeRestriction
