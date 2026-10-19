import Parafree.TheoremA.DividedPresentation
import Parafree.Linear.SubmoduleFamilies
import Parafree.Linear.ModScalar
import Parafree.Linear.CommonPresentation

/-! The actual divided model modulo two as the direct sum of its reduced
filtration layers. Both surjectivity and injectivity use finite representatives. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Linear
open Auxiliary (dividedFiltration)

abbrev FilteredFamilies := Π₀ n, dividedFiltration n

def dividedTerm (n : ℕ) : dividedFiltration n →ₗ[ℤ] dividedAlgebra :=
  (((1 / 2 : ℚ) ^ n • integralInclusion.toLinearMap).comp
    (dividedFiltration n).subtype).codRestrict _ (fun a => term_mem_span n a a.property)

@[simp] theorem dividedTerm_coe (n : ℕ) (a : dividedFiltration n) :
    (dividedTerm n a : Ambient) = (1 / 2 : ℚ) ^ n • integralInclusion a := rfl

def sumTerms : FilteredFamilies →ₗ[ℤ] dividedAlgebra :=
  DFinsupp.lsum ℤ dividedTerm

@[simp] theorem sumTerms_single (n : ℕ) (a : dividedFiltration n) :
    sumTerms (DFinsupp.single n a) = dividedTerm n a :=
  DFinsupp.lsum_single ℤ dividedTerm n a

theorem sumTerms_eq_presentation : sumTerms =
    dividedPresentation.comp (submoduleFamily dividedFiltration) := by
  apply DFinsupp.lhom_ext
  intro n a
  apply Subtype.ext
  rw [sumTerms_single]
  change (1 / 2 : ℚ) ^ n • integralInclusion a =
    Auxiliary.dividedValue (submoduleFamilyValue dividedFiltration (DFinsupp.single n a))
  rw [submoduleFamilyValue_single, dividedValue_single]

theorem sumTerms_surjective : Function.Surjective sumTerms := by
  have hspan : dividedSpan ≤ LinearMap.range
      (dividedAlgebra.toSubmodule.subtype.comp sumTerms) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, a, ha, rfl⟩
    exact ⟨DFinsupp.single n ⟨a, ha⟩, congrArg Subtype.val (sumTerms_single n ⟨a, ha⟩)⟩
  intro y
  obtain ⟨a, ha⟩ := hspan y.property
  exact ⟨a, Subtype.ext ha⟩

/-- Relations in a layer: the next filtration term and twice the current one. -/
def reducedLayerRelations (n : ℕ) : Submodule ℤ (dividedFiltration n) :=
  (dividedFiltration (n + 1)).comap (dividedFiltration n).subtype ⊔
    ModScalar.multiples (2 : ℤ) (dividedFiltration n)

abbrev ReducedLayer (n : ℕ) := dividedFiltration n ⧸ reducedLayerRelations n
abbrev ReducedGraded := Π₀ n, ReducedLayer n

theorem mem_reducedLayerRelations (n : ℕ) (x : dividedFiltration n) :
    x ∈ reducedLayerRelations n ↔
      ∃ a ∈ dividedFiltration (n + 1), ∃ b ∈ dividedFiltration n,
        (x : Auxiliary.Free ℤ) = a + (2 : ℤ) • b := by
  rw [reducedLayerRelations, Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, ⟨c, hc⟩, h⟩
    refine ⟨a, ha, c, c.property, ?_⟩
    rw [← h, ← hc]
    rfl
  · rintro ⟨a, ha, b, hb, h⟩
    have ha' := Auxiliary.dividedFiltration_antitone (Nat.le_succ n) ha
    exact ⟨⟨a, ha'⟩, ha, (2 : ℤ) • (⟨b, hb⟩ : dividedFiltration n),
      ⟨⟨b, hb⟩, rfl⟩, Subtype.ext h.symm⟩

def gradedPresentation : FilteredFamilies →ₗ[ℤ] ReducedGraded :=
  DFinsupp.mapRange.linearMap (fun n => (reducedLayerRelations n).mkQ)

@[simp] theorem gradedPresentation_apply (x : FilteredFamilies) (n : ℕ) :
    gradedPresentation x n = (reducedLayerRelations n).mkQ (x n) := rfl

theorem gradedPresentation_surjective : Function.Surjective gradedPresentation := by
  intro x
  induction x using DFinsupp.induction with
  | h0 => exact ⟨0, map_zero _⟩
  | @ha n a x _ _ ih =>
    obtain ⟨b, rfl⟩ := (reducedLayerRelations n).mkQ_surjective a
    obtain ⟨y, rfl⟩ := ih
    refine ⟨DFinsupp.single n b + y, ?_⟩
    rw [map_add]
    congr 1
    ext j
    by_cases h : j = n
    · subst j; simp only [gradedPresentation_apply, DFinsupp.single_eq_same]
    · simp only [gradedPresentation_apply, DFinsupp.single_eq_of_ne h, map_zero]

abbrev ReducedDivided := ModScalar.Quotient (2 : ℤ) dividedAlgebra

def reductionPresentation : FilteredFamilies →ₗ[ℤ] ReducedDivided :=
  (ModScalar.mk (2 : ℤ) dividedAlgebra).comp sumTerms

theorem reductionPresentation_surjective : Function.Surjective reductionPresentation :=
  (ModScalar.mk_surjective (2 : ℤ) dividedAlgebra).comp sumTerms_surjective

theorem dividedTerm_next (n : ℕ) (a : dividedFiltration (n + 1)) :
    dividedTerm n ⟨a, Auxiliary.dividedFiltration_antitone (Nat.le_succ n) a.property⟩ =
      (2 : ℤ) • dividedTerm (n + 1) a := by
  apply Subtype.ext
  change (1 / 2 : ℚ) ^ n • integralInclusion a =
    (2 : ℤ) • ((1 / 2 : ℚ) ^ (n + 1) • integralInclusion a)
  rw [two_smul, ← add_smul, pow_succ]
  congr 1
  ring

theorem dividedTerm_relation (n : ℕ) (a : dividedFiltration n)
    (ha : a ∈ reducedLayerRelations n) :
    ModScalar.mk (2 : ℤ) dividedAlgebra (dividedTerm n a) = 0 := by
  obtain ⟨b, hb, c, hc, he⟩ := (mem_reducedLayerRelations n a).mp ha
  let b' : dividedFiltration (n + 1) := ⟨b, hb⟩
  let c' : dividedFiltration n := ⟨c, hc⟩
  have h : a = ⟨b, Auxiliary.dividedFiltration_antitone (Nat.le_succ n) hb⟩ +
      (2 : ℤ) • c' := Subtype.ext he
  rw [h, map_add, map_smul, dividedTerm_next n b', ← smul_add]
  exact ModScalar.mk_smul_self (2 : ℤ) dividedAlgebra _

/-- Denominator cancellation gives the exact kernel, not only one inclusion. -/
theorem reductionPresentation_ker : LinearMap.ker reductionPresentation =
    LinearMap.ker gradedPresentation := by
  ext x
  constructor
  · intro hx
    change ModScalar.mk (2 : ℤ) dividedAlgebra (sumTerms x) = 0 at hx
    obtain ⟨y, hy⟩ := (ModScalar.mk_eq_zero (2 : ℤ) dividedAlgebra _).mp hx
    have heven : ∃ y : dividedAlgebra,
        dividedPresentation (submoduleFamily dividedFiltration x) = (2 : ℤ) • y := by
      exact ⟨y, (LinearMap.congr_fun sumTerms_eq_presentation x).symm.trans hy.symm⟩
    apply DFinsupp.ext
    intro n
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (mem_reducedLayerRelations n (x n)).mpr
    simpa only [submoduleFamily_apply] using
      dividedPresentation_even_coefficients (submoduleFamily dividedFiltration x) heven n
  · intro hx
    have hcoords : ∀ n, x n ∈ reducedLayerRelations n := by
      intro n
      exact (Submodule.Quotient.mk_eq_zero _).mp
        (congrArg (fun z : ReducedGraded => z n) hx)
    clear hx
    induction x using DFinsupp.induction with
    | h0 => exact map_zero _
    | @ha n a x hxn _ ih =>
      have ha : a ∈ reducedLayerRelations n := by
        simpa only [DFinsupp.add_apply, DFinsupp.single_eq_same, hxn, add_zero] using hcoords n
      have hx : ∀ j, x j ∈ reducedLayerRelations j := by
        intro j
        by_cases h : j = n
        · subst j; rw [hxn]; exact (reducedLayerRelations n).zero_mem
        · simpa only [DFinsupp.add_apply, DFinsupp.single_eq_of_ne h, zero_add] using hcoords j
      change reductionPresentation (DFinsupp.single n a + x) = 0
      rw [map_add, ih hx, add_zero]
      change ModScalar.mk (2 : ℤ) dividedAlgebra (sumTerms (DFinsupp.single n a)) = 0
      rw [sumTerms_single]
      exact dividedTerm_relation n a ha

/-- The direct sum of the actual reduced layers is the actual divided model modulo two. -/
@[irreducible] def dividedReductionEquiv : ReducedGraded ≃ₗ[ℤ] ReducedDivided :=
  equivOfCommonPresentation (R := ℤ) (M := FilteredFamilies) (N := ReducedGraded)
    (P := ReducedDivided) gradedPresentation reductionPresentation
    gradedPresentation_surjective reductionPresentation_surjective reductionPresentation_ker.symm

theorem dividedReductionEquiv_presentation (x : FilteredFamilies) :
    dividedReductionEquiv (gradedPresentation x) = reductionPresentation x := by
  unfold dividedReductionEquiv
  exact
  equivOfCommonPresentation_apply (R := ℤ) (M := FilteredFamilies) (N := ReducedGraded)
    (P := ReducedDivided) gradedPresentation reductionPresentation
    gradedPresentation_surjective reductionPresentation_surjective reductionPresentation_ker.symm x

end Parafree.TheoremA.RationalModel
