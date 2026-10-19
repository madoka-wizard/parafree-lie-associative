import Parafree.Associative.RelativePBW
import Parafree.Linear.SplitBasis
import Parafree.Homology.Coefficients.FreeEnveloping
import Parafree.Homology.Coefficients.AssociativeRestriction

/-! Restriction of the regular enveloping module along a split inclusion.
PBW supplies the actual equivariant regular-module decomposition, not just
freeness over the base ring. -/

noncomputable section

namespace Parafree.Homology.Coefficients.RelativeEnveloping

open scoped DirectSum
open Module LieRings
open Parafree.Associative
open AssociativeRestriction

universe u
variable {R J L ι κ : Type u} [CommRing R]
  [LieRing J] [LieAlgebra R J] [LieRing L] [LieAlgebra R L]
  [LinearOrder ι] [LinearOrder κ]
  (f : J →ₗ⁅R⁆ L) (b : Basis ι R J) (B : Basis (ι ⊕ₗ κ) R L)

abbrev action : J →ₗ⁅R⁆ UEA R L := (UniversalEnvelopingAlgebra.ι R).comp f

abbrev Restricted := Coefficients (action f) (UEA R L)

open Classical in
def decompositionLinear : (⨁ _ : κ →₀ ℕ, Enveloping.Regular R J) ≃ₗ[R] Restricted f :=
  (finsuppLEquivDirectSum R (Enveloping.Regular R J) (κ →₀ ℕ)).symm.trans
    ((Finsupp.mapRange.linearEquiv (Enveloping.equiv R J)).trans
      ((RelativePBW.equiv b B).trans (AssociativeRestriction.equiv (action f) _).symm))

open Classical in
theorem decompositionLinear_lof
    (hB : ∀ i, B (toLex (Sum.inl i)) = f (b i))
    (q : κ →₀ ℕ) (a : Enveloping.Regular R J) :
    AssociativeRestriction.equiv (action f) _
      (decompositionLinear f b B (DirectSum.lof R _ _ q a)) =
        RelativePBW.inclusion f (Enveloping.equiv R J a) * RelativePBW.complement B q := by
  simp only [decompositionLinear, LinearEquiv.trans_apply,
    finsuppLEquivDirectSum_symm_lof, Finsupp.mapRange.linearEquiv_apply,
    Finsupp.mapRange_single, LinearEquiv.apply_symm_apply]
  exact RelativePBW.equiv_single f b B hB q _

open Classical in
/-- PBW decomposition with its left Lie-module action. -/
def decomposition (hB : ∀ i, B (toLex (Sum.inl i)) = f (b i)) :
    (⨁ _ : κ →₀ ℕ, Enveloping.Regular R J) ≃ₗ⁅R,J⁆ Restricted f :=
  { decompositionLinear f b B with
    map_lie' := by
      intro x m
      change decompositionLinear f b B ⁅x, m⁆ = ⁅x, decompositionLinear f b B m⁆
      induction m using DirectSum.induction_on with
      | zero => simp
      | add a c ha hc => simp only [lie_add, map_add, ha, hc]
      | of q a =>
        have h := (DirectSum.lieModuleOf R (κ →₀ ℕ) J
          (fun _ => Enveloping.Regular R J) q).map_lie x a
        change DirectSum.lof R (κ →₀ ℕ) (fun _ => Enveloping.Regular R J) q ⁅x, a⁆ =
          ⁅x, DirectSum.lof R (κ →₀ ℕ) (fun _ => Enveloping.Regular R J) q a⁆ at h
        change decompositionLinear f b B
          ⁅x, DirectSum.lof R (κ →₀ ℕ) (fun _ => Enveloping.Regular R J) q a⁆ =
            ⁅x, decompositionLinear f b B
              (DirectSum.lof R (κ →₀ ℕ) (fun _ => Enveloping.Regular R J) q a)⁆
        rw [← h]
        apply (AssociativeRestriction.equiv (action f) _).injective
        rw [decompositionLinear_lof f b B hB, AssociativeRestriction.equiv_lie,
          decompositionLinear_lof f b B hB, Enveloping.equiv_lie, map_mul,
          RelativePBW.inclusion_iota]
        exact mul_assoc _ _ _ }

section Ideal



open Classical in
/-- The ideal and its quotient need only be free as base-ring modules. -/
theorem exists_ideal_decomposition (I : LieIdeal R L)
    [Module.Free R I] [Module.Free R (L ⧸ I)] :
    ∃ σ : Type u, Nonempty ((⨁ _ : σ, Enveloping.Regular R I) ≃ₗ⁅R,I⁆ Restricted I.incl) := by
  letI : LinearOrder (Module.Free.ChooseBasisIndex R I) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  letI : LinearOrder (Module.Free.ChooseBasisIndex R (L ⧸ I)) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  let b := Module.Free.chooseBasis R I
  let c := Module.Free.chooseBasis R (L ⧸ I)
  let B := Parafree.Linear.SplitBasis.basis I.toSubmodule b c
  refine ⟨Module.Free.ChooseBasisIndex R (L ⧸ I) →₀ ℕ, ⟨decomposition I.incl b B ?_⟩⟩
  intro i
  exact Parafree.Linear.SplitBasis.basis_inl I.toSubmodule b c i

/-- Restricting the ambient enveloping algebra to such an ideal is acyclic
in positive CE degrees. -/
theorem ideal_exactAt (I : LieIdeal R L) [Module.Free R I] [Module.Free R (L ⧸ I)]
    (n : ℕ) (hn : n ≠ 0) : (complex R I (Restricted I.incl)).ExactAt n := by
  classical
  obtain ⟨σ, ⟨e⟩⟩ := exists_ideal_decomposition I
  exact Enveloping.exactAt_of_regular_equiv e.symm n hn

theorem ideal_homology_isZero (I : LieIdeal R L) [Module.Free R I]
    [Module.Free R (L ⧸ I)] (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (homology R I (Restricted I.incl) n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (ideal_exactAt I n hn)

end Ideal

end Parafree.Homology.Coefficients.RelativeEnveloping
