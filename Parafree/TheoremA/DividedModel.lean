import Parafree.TheoremA.DividedRepresentatives
import Parafree.Lie.IdealFiltration

/-! Identification of the faithful rational model with the span of divided
lower-central relation terms. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie
open Auxiliary (dividedFiltration)

private theorem filtration_eq (n : ℕ) :
    dividedFiltration n = (idealPowerFiltration (Auxiliary.relationIdeal ℤ) n).toSubmodule := by
  cases n with
  | zero => rfl
  | succ n => exact (idealLowerCentral_toSubmodule _ n).symm

theorem dividedFiltration_lie_mem (i j : ℕ) {a b : Auxiliary.Free ℤ}
    (ha : a ∈ dividedFiltration i) (hb : b ∈ dividedFiltration j) :
    ⁅a, b⁆ ∈ dividedFiltration (i + j) := by
  rw [filtration_eq] at ha hb ⊢
  exact (idealPowerFiltration_bracket _ i j) (LieSubmodule.lie_mem_lie ha hb)

def dividedTerms : Set Ambient :=
  {v | ∃ n a, a ∈ dividedFiltration n ∧ (1 / 2 : ℚ) ^ n • integralInclusion a = v}

def dividedSpan : Submodule ℤ Ambient := Submodule.span ℤ dividedTerms

theorem term_mem_span (n : ℕ) (a : Auxiliary.Free ℤ) (ha : a ∈ dividedFiltration n) :
    (1 / 2 : ℚ) ^ n • integralInclusion a ∈ dividedSpan :=
  Submodule.subset_span ⟨n, a, ha, rfl⟩

private theorem span_lie_mem {a b : Ambient} (ha : a ∈ dividedSpan) (hb : b ∈ dividedSpan) :
    ⁅a, b⁆ ∈ dividedSpan := by
  refine Submodule.span_induction₂ (p := fun a b _ _ => ⁅a, b⁆ ∈ dividedSpan)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro _ _ ⟨i, a, ha, rfl⟩ ⟨j, b, hb, rfl⟩
    rw [smul_lie, lie_smul, smul_smul, ← pow_add, ← LieHom.map_lie]
    exact term_mem_span (i + j) ⁅a, b⁆ (dividedFiltration_lie_mem i j ha hb)
  · intro a _; simpa only [zero_lie] using dividedSpan.zero_mem
  · intro a _; simpa only [lie_zero] using dividedSpan.zero_mem
  · intro a b c _ _ _ ha hb
    simpa only [add_lie] using dividedSpan.add_mem ha hb
  · intro a b c _ _ _ ha hb
    simpa only [lie_add] using dividedSpan.add_mem ha hb
  · intro r a b _ _ h
    simpa only [smul_lie] using dividedSpan.smul_mem r h
  · intro r a b _ _ h
    simpa only [lie_smul] using dividedSpan.smul_mem r h

def dividedAlgebra : LieSubalgebra ℤ Ambient :=
  { dividedSpan with lie_mem' := span_lie_mem }

theorem x_mem_span (i : Fin 3) : x i ∈ dividedSpan := by
  have h := term_mem_span 0 (Auxiliary.generator ℤ i) Submodule.mem_top
  simpa only [pow_zero, one_smul, integralInclusion, Auxiliary.generator,
    FreeScalarExtension.generatorMap_of, x] using h

theorem q_mem_span (i : Fin 3) : q i ∈ dividedSpan := by
  have hi : Auxiliary.relator ℤ i ∈ dividedFiltration 1 := by
    apply (Auxiliary.mem_dividedFiltration_succ 0 _).mpr
    exact ⟨LieSubmodule.subset_lieSpan (Set.mem_range_self i), LieSubmodule.mem_top _⟩
  simpa only [pow_one, q] using term_mem_span 1 (Auxiliary.relator ℤ i) hi

/-- Every integral ambient element belongs to the realization's range. -/
theorem integral_mem_range (a : Auxiliary.Free ℤ) : integralInclusion a ∈ realization.range := by
  let f : Auxiliary.Free ℤ →ₗ⁅ℤ⁆ L := FreeLieAlgebra.lift ℤ (fun i => toL (K.x i))
  have h : realization.comp f = integralInclusion := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change realization (f (FreeLieAlgebra.of ℤ i)) = _
    rw [show f (FreeLieAlgebra.of ℤ i) = toL (K.x i) from FreeLieAlgebra.lift_of_apply _ _,
      realization_x]
    exact (FreeScalarExtension.generatorMap_of ℚ (Fin 3) i).symm
  exact ⟨f a, LieHom.congr_fun h a⟩

/-- Half of every element of the relation ideal is in the actual range. -/
theorem half_relation_mem_range (a : Auxiliary.Free ℤ) (ha : a ∈ Auxiliary.relationIdeal ℤ) :
    (1 / 2 : ℚ) • integralInclusion a ∈ realization.range := by
  refine LieSubmodule.lieSpan_induction (R := ℤ) (L := Auxiliary.Free ℤ)
    (p := fun a _ => (1 / 2 : ℚ) • integralInclusion a ∈ realization.range)
    ?_ ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩
    exact ⟨toL (K.q i), realization_q i⟩
  · simp only [map_zero, smul_zero]
    exact realization.range.zero_mem
  · intro a b _ _ ha hb
    simpa only [map_add, smul_add] using realization.range.add_mem ha hb
  · intro r a _ ha
    rw [map_smul, smul_comm]
    exact realization.range.smul_mem r ha
  · intro a b _ hb
    rw [LieHom.map_lie, ← lie_smul]
    exact realization.range.lie_mem (integral_mem_range a) hb

/-- Every divided lower-central relation term belongs to the actual range. -/
theorem lowerCentral_divided_mem_range (n : ℕ) (a : Auxiliary.relationIdeal ℤ)
    (ha : a ∈ lowerCentral ℤ (Auxiliary.relationIdeal ℤ) n) :
    (1 / 2 : ℚ) ^ (n + 1) • integralInclusion (a : Auxiliary.Free ℤ) ∈ realization.range := by
  induction n generalizing a with
  | zero => simpa only [Nat.zero_add, pow_one] using half_relation_mem_range a a.property
  | succ n ih =>
    change a ∈ (lowerCentral ℤ (Auxiliary.relationIdeal ℤ) (n + 1)).toSubmodule at ha
    rw [lowerCentral, LieModule.lowerCentralSeries_succ,
      LieSubmodule.lieIdeal_oper_eq_linear_span'] at ha
    refine Submodule.span_induction (p := fun (a : Auxiliary.relationIdeal ℤ) _ =>
      (1 / 2 : ℚ) ^ (n + 1 + 1) • integralInclusion (a : Auxiliary.Free ℤ) ∈
        realization.range) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨r, _, s, hs, rfl⟩
      have hbr := realization.range.lie_mem (half_relation_mem_range r r.property) (ih s hs)
      change (1 / 2 : ℚ) ^ (n + 1 + 1) • integralInclusion ⁅(r : Auxiliary.Free ℤ), (s : Auxiliary.Free ℤ)⁆ ∈ _
      simpa only [smul_lie, lie_smul, smul_smul, ← LieHom.map_lie, pow_succ] using hbr
    · change (1 / 2 : ℚ) ^ (n + 1 + 1) • integralInclusion (0 : Auxiliary.Free ℤ) ∈ _
      simp only [map_zero, smul_zero]
      exact realization.range.zero_mem
    · intro a b _ _ ha hb
      change (1 / 2 : ℚ) ^ (n + 1 + 1) • integralInclusion ((a : Auxiliary.Free ℤ) + (b : Auxiliary.Free ℤ)) ∈ _
      simpa only [map_add, smul_add] using realization.range.add_mem ha hb
    · intro r a _ ha
      change (1 / 2 : ℚ) ^ (n + 1 + 1) • integralInclusion (r • (a : Auxiliary.Free ℤ)) ∈ _
      rw [map_smul, smul_comm]
      exact realization.range.smul_mem r ha

/-- The divided span is contained in the range without any completion. -/
theorem span_le_range : dividedSpan ≤ realization.range.toSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, a, ha, rfl⟩
  cases n with
  | zero => simpa only [pow_zero, one_smul] using integral_mem_range a
  | succ n =>
    obtain ⟨haI, ha⟩ := (Auxiliary.mem_dividedFiltration_succ n a).mp ha
    exact lowerCentral_divided_mem_range n ⟨a, haI⟩ ha

/-- Conversely, the six actual presentation generators lie in the divided algebra. -/
theorem range_le_span : realization.range.toSubmodule ≤ dividedSpan := by
  let xs : Fin 3 → dividedAlgebra := fun i => ⟨x i, x_mem_span i⟩
  let qs : Fin 3 → dividedAlgebra := fun i => ⟨q i, q_mem_span i⟩
  have heq : equationStep qs xs = xs := by
    funext i
    apply Subtype.ext
    have hi := congrFun equations i
    fin_cases i <;> simpa only [equationStep, xs, qs] using hi
  let f := K.lift qs xs heq
  have h : dividedAlgebra.incl.comp f = evaluation := by
    apply K.hom_ext
    · intro i
      change (f (K.x i) : Ambient) = evaluation (K.x i)
      rw [K.lift_x, evaluation_x]
    · intro i
      change (f (K.q i) : Ambient) = evaluation (K.q i)
      rw [K.lift_q, evaluation_q]
  rintro _ ⟨a, rfl⟩
  obtain ⟨a, rfl⟩ := quotientMk_surjective (residualIdeal ℤ K) a
  change evaluation a ∈ dividedSpan
  rw [← LieHom.congr_fun h a]
  exact (f a).property

/-- The sum of divided filtration terms is exactly the faithful model of `L`. -/
theorem range_eq_dividedSpan : realization.range.toSubmodule = dividedSpan :=
  le_antisymm range_le_span span_le_range

/-- The actual residual quotient, with codomain restricted to the divided model. -/
def toDivided : L →ₗ⁅ℤ⁆ dividedAlgebra where
  toFun a := ⟨realization a, range_le_span ⟨a, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add realization a b)
  map_smul' r a := Subtype.ext (map_smul realization r a)
  map_lie' {a b} := Subtype.ext (realization.map_lie a b)

/-- A Lie equivalence with the divided model, with no additional assumptions. -/
def equivDivided : L ≃ₗ⁅ℤ⁆ dividedAlgebra :=
  LieEquiv.ofBijective toDivided ⟨
    fun a b h => realization_injective (congrArg Subtype.val h),
    fun b => by
      obtain ⟨a, ha⟩ := span_le_range b.property
      exact ⟨a, Subtype.ext ha⟩⟩

end Parafree.TheoremA.RationalModel
