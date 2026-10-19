import Parafree.Homology.Coefficients.FoxSequence

/-! Exactness of the explicit derivative sequence, using only the first CE
boundary and the last-letter product rule. No categorical connecting-map
identification is needed. -/

noncomputable section

namespace Parafree.Homology.Coefficients.FoxSequence

open Parafree.Associative
open Parafree.Linear.ExteriorTensor
open FreeAssociative
open scoped TensorProduct

universe u
variable (R X : Type u) [CommRing R]
  (J : LieIdeal R (FreeLieAlgebra R X))

/-- Last-letter differentiation of arbitrary associative coefficients, modulo ideal action. -/
def derivativeClass : A R X J →ₗ[R] Q R X J :=
  (actionSpan R J (B R X J)).mkQ.comp (retraction (idealAction R X J))

private theorem action_class_zero (j : J) (b : B R X J) :
    (Submodule.Quotient.mk ⁅j, b⁆ : Q R X J) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨j, b, rfl⟩)

theorem derivativeClass_action (j : J) (a : A R X J) :
    derivativeClass R X J ⁅j, a⁆ =
      FreeAlgebra.algebraMapInv (AssociativeRestriction.equiv (idealAction R X J) _ a) •
        representative R X J j := by
  change (actionSpan R J (B R X J)).mkQ
    ((AssociativeRestriction.equiv (idealAction R X J) _).symm
      (FreeAugmentation.derivative R X (idealAction R X J j *
        AssociativeRestriction.equiv (idealAction R X J) _ a))) = _
  rw [FreeAugmentation.derivative_mul, map_add, map_add]
  change (Submodule.Quotient.mk ⁅j, retraction (idealAction R X J) a⁆ : Q R X J) + _ = _
  rw [action_class_zero, zero_add]
  exact map_smul ((actionSpan R J (B R X J)).mkQ.comp
    (AssociativeRestriction.equiv (idealAction R X J) _).symm.toLinearMap) _ _

/-- The product rule is exactly the representative-level connecting formula. -/
theorem derivativeClass_differential (c : Chain R J (A R X J) 1) :
    derivativeClass R X J (zeroChainEquiv R J (A R X J)
      (differential R J (A R X J) 0 c)) =
        -representative R X J (oneAugmentation R X J c) := by
  induction c using TensorProduct.induction_on with
  | zero =>
    rw [map_zero (differential R J (A R X J) 0),
      (zeroChainEquiv R J (A R X J)).map_zero,
      (derivativeClass R X J).map_zero, (oneAugmentation R X J).map_zero,
      (representative R X J).map_zero, neg_zero]
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]
  | tmul w a =>
    have hw : w = exteriorPower.ιMulti R 1 ![(exteriorPower.oneEquiv R J) w] := by
      apply (exteriorPower.oneEquiv R J).injective
      simp only [exteriorPower.oneEquiv_ιMulti]
      rfl
    rw [hw]
    change derivativeClass R X J (zeroChainEquiv R J (A R X J)
      (differential R J (A R X J) 0
        (pure R J (A R X J) 1 ![(exteriorPower.oneEquiv R J) w] a))) = _
    rw [zeroChainEquiv_differential_pure, map_neg, derivativeClass_action]
    change _ = -representative R X J
      (oneAugmentation R X J (pure R J (A R X J) 1 ![(exteriorPower.oneEquiv R J) w] a))
    rw [oneAugmentation_pure, map_smul]

private theorem inclusion_actionSpan :
    actionSpan R J (B R X J) ≤ (actionSpan R J (A R X J)).comap
      (inclusion (idealAction R X J)).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro b ⟨j, b, rfl⟩
  change inclusion (idealAction R X J) ⁅j,b⁆ ∈ actionSpan R J (A R X J)
  rw [LieModuleHom.map_lie]
  exact Submodule.subset_span ⟨j, inclusion (idealAction R X J) b, rfl⟩

/-- Concatenation on the actual coinvariants. -/
def multiplication : Q R X J →ₗ[R] Coinvariants R J (A R X J) :=
  (actionSpan R J (B R X J)).mapQ (actionSpan R J (A R X J))
    (inclusion (idealAction R X J)).toLinearMap (inclusion_actionSpan R X J)

@[simp] theorem multiplication_mk (b : B R X J) :
    multiplication R X J (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (inclusion (idealAction R X J) b) := rfl

theorem derivativeClass_inclusion (b : B R X J) :
    derivativeClass R X J (inclusion (idealAction R X J) b) = Submodule.Quotient.mk b := by
  change (actionSpan R J (B R X J)).mkQ
    (retraction (idealAction R X J) (inclusion (idealAction R X J) b)) = _
  have h := LinearMap.congr_fun (retraction_inclusion (idealAction R X J)) b
  change retraction (idealAction R X J) (inclusion (idealAction R X J) b) = b at h
  rw [h]
  rfl

theorem multiplication_representative (j : J) :
    multiplication R X J (representative R X J j) = 0 := by
  change (Submodule.Quotient.mk (inclusion (idealAction R X J) (derivative R X J j)) :
    Coinvariants R J (A R X J)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have h : inclusion (idealAction R X J) (derivative R X J j) =
      ⁅j, (AssociativeRestriction.equiv (idealAction R X J) _).symm 1⁆ := by
    change FreeAugmentation.concatenate R X (FreeAugmentation.derivative R X (idealAction R X J j)) =
      idealAction R X J j * 1
    rw [FreeAugmentation.concatenate_derivative, augmentation_idealAction, map_zero, sub_zero, mul_one]
  rw [h]
  exact Submodule.subset_span ⟨j, _, rfl⟩

/-- Exactness for the concrete derivative and concrete concatenation maps. -/
theorem relationMap_exact : Function.Exact (relationMap R X J) (multiplication R X J) := by
  intro q
  constructor
  · intro hq
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (actionSpan R J (B R X J)) q
    have hb : inclusion (idealAction R X J) b ∈ actionSpan R J (A R X J) :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    rw [← differential_zero_range_map R J (A R X J)] at hb
    obtain ⟨a, ⟨c, rfl⟩, hc⟩ := hb
    refine ⟨Submodule.Quotient.mk (-oneAugmentation R X J c), ?_⟩
    rw [relationMap_mk]
    erw [map_neg]
    rw [← derivativeClass_differential]
    change zeroChainEquiv R J (A R X J) (differential R J (A R X J) 0 c) =
      inclusion (idealAction R X J) b at hc
    rw [hc, derivativeClass_inclusion]
    rfl
  · rintro ⟨a, rfl⟩
    obtain ⟨j, rfl⟩ := Submodule.mkQ_surjective
      (⁅(⊤ : LieIdeal R J), (⊤ : LieIdeal R J)⁆).toSubmodule a
    exact multiplication_representative R X J j

end Parafree.Homology.Coefficients.FoxSequence
