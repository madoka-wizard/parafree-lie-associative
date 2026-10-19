import Parafree.TheoremB.Identities
import Parafree.Lie.FreeScalarExtension
import Parafree.Lie.FreeResidual

/-! The exact rational Lie ring in Theorem B and a faithful integral model.
Only the second free generator is dilated, so no denominator remains in the
four generators of the integral model. -/

noncomputable section
namespace Parafree.TheoremB

open Parafree.Lie

abbrev Ambient := FreeLieAlgebra ℚ (Fin 2)
abbrev IntegralFree := FreeLieAlgebra ℤ (Fin 2)

def ambientT : Ambient := FreeLieAlgebra.of ℚ 0
def ambientA : Ambient := FreeLieAlgebra.of ℚ 1

def generators : Fin 4 → Ambient :=
  ![ambientT, ambientA, (1 / 5 : ℚ) • f₁ ambientT ambientA,
    (1 / 5 : ℚ) • f₂ ambientT ambientA]

/-- The Lie subring specified in the manuscript, with precisely its four generators. -/
def algebra : LieSubalgebra ℤ Ambient := LieSubalgebra.lieSpan ℤ Ambient (Set.range generators)
abbrev P := algebra

def generator (i : Fin 4) : P :=
  ⟨generators i, LieSubalgebra.subset_lieSpan (Set.mem_range_self i)⟩

abbrev t : P := generator 0
abbrev a : P := generator 1
abbrev u : P := generator 2
abbrev v : P := generator 3

def x : P := a - (2 : ℤ) • u

def freeToP : IntegralFree →ₗ⁅ℤ⁆ P := FreeLieAlgebra.lift ℤ ![t, x]

def integralT : IntegralFree := FreeLieAlgebra.of ℤ 0
def integralA : IntegralFree := FreeLieAlgebra.of ℤ 1

def integralGenerators : Fin 4 → IntegralFree :=
  ![integralT, (5 : ℤ) • integralA, f₁ integralT integralA,
    (5 : ℤ) • h integralT integralA - (25 : ℤ) • c integralT integralA]

def integralAlgebra : LieSubalgebra ℤ IntegralFree :=
  LieSubalgebra.lieSpan ℤ IntegralFree (Set.range integralGenerators)
abbrev Q := integralAlgebra

def integralGenerator (i : Fin 4) : Q :=
  ⟨integralGenerators i, LieSubalgebra.subset_lieSpan (Set.mem_range_self i)⟩

/-- Undo the dilation of the second generator. -/
def evaluate : IntegralFree →ₗ⁅ℤ⁆ Ambient :=
  FreeLieAlgebra.lift ℤ ![ambientT, (1 / 5 : ℚ) • ambientA]

@[simp] theorem evaluate_t : evaluate integralT = ambientT := FreeLieAlgebra.lift_of_apply _ _
@[simp] theorem evaluate_a : evaluate integralA = (1 / 5 : ℚ) • ambientA :=
  FreeLieAlgebra.lift_of_apply _ _

def dilation : Ambient →ₗ⁅ℤ⁆ Ambient :=
  { (FreeLieAlgebra.lift ℚ ![ambientT, (5 : ℚ) • ambientA]).toLinearMap.restrictScalars ℤ with
    map_lie' := (FreeLieAlgebra.lift ℚ ![ambientT, (5 : ℚ) • ambientA]).map_lie _ _ }

theorem dilation_evaluate : dilation.comp evaluate = FreeScalarExtension.generatorMap ℚ (Fin 2) := by
  apply FreeLieAlgebra.hom_ext
  intro i
  change dilation (evaluate (FreeLieAlgebra.of ℤ i)) =
    FreeScalarExtension.generatorMap ℚ (Fin 2) (FreeLieAlgebra.of ℤ i)
  rw [FreeScalarExtension.generatorMap_of]
  fin_cases i
  · change dilation (evaluate integralT) = ambientT
    rw [evaluate_t]
    exact FreeLieAlgebra.lift_of_apply _ _
  · change dilation (evaluate integralA) = ambientA
    rw [evaluate_a]
    change FreeLieAlgebra.lift ℚ ![ambientT, (5 : ℚ) • ambientA]
      ((1 / 5 : ℚ) • ambientA) = ambientA
    rw [map_smul]
    change (1 / 5 : ℚ) • (FreeLieAlgebra.lift ℚ ![ambientT, (5 : ℚ) • ambientA]
      (FreeLieAlgebra.of ℚ 1)) = ambientA
    rw [FreeLieAlgebra.lift_of_apply]
    norm_num [smul_smul]

theorem evaluate_injective : Function.Injective evaluate := by
  intro b d he
  apply FreeScalarExtension.generatorMap_injective ℚ (Fin 2)
  simpa only [← dilation_evaluate, LieHom.comp_apply] using congrArg dilation he

theorem evaluate_generators (i : Fin 4) : evaluate (integralGenerators i) = generators i := by
  fin_cases i
  · exact evaluate_t
  · change evaluate ((5 : ℤ) • integralA) = ambientA
    rw [map_smul, evaluate_a]
    norm_num [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  · change evaluate (f₁ integralT integralA) = (1 / 5 : ℚ) • f₁ ambientT ambientA
    rw [map_f₁, evaluate_t, evaluate_a, f₁_smul]
  · change evaluate ((5 : ℤ) • h integralT integralA - (25 : ℤ) • c integralT integralA) =
      (1 / 5 : ℚ) • f₂ ambientT ambientA
    rw [map_sub, map_smul, map_smul, map_h, map_c, evaluate_t, evaluate_a, h_smul, c_smul]
    simp only [← Int.cast_smul_eq_zsmul ℚ, smul_smul, f₂, smul_sub]
    norm_num

theorem evaluate_mem {b : IntegralFree} (hb : b ∈ integralAlgebra) : evaluate b ∈ algebra := by
  have hh : integralAlgebra ≤ algebra.comap evaluate := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    change evaluate (integralGenerators i) ∈ algebra
    rw [evaluate_generators]
    exact LieSubalgebra.subset_lieSpan (Set.mem_range_self i)
  exact hh hb

def integralToP : Q →ₗ⁅ℤ⁆ P where
  toFun b := ⟨evaluate b, evaluate_mem b.property⟩
  map_add' b d := Subtype.ext (map_add evaluate (b : IntegralFree) (d : IntegralFree))
  map_smul' r b := Subtype.ext (map_smul evaluate r (b : IntegralFree))
  map_lie' := Subtype.ext (evaluate.map_lie _ _)

@[simp] theorem integralToP_generator (i : Fin 4) :
    integralToP (integralGenerator i) = generator i := Subtype.ext (evaluate_generators i)

theorem integralToP_bijective : Function.Bijective integralToP := by
  refine ⟨fun b d he => Subtype.ext (evaluate_injective (congrArg Subtype.val he)), ?_⟩
  intro b
  have hb : b.val ∈ (algebra.incl.comp integralToP).range := by
    have hh : algebra ≤ (algebra.incl.comp integralToP).range := by
      apply LieSubalgebra.lieSpan_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨integralGenerator i, evaluate_generators i⟩
    exact hh b.property
  obtain ⟨d, hd⟩ := hb
  exact ⟨d, Subtype.ext hd⟩

/-- Identification with the actual rational Lie subring, not a new presentation. -/
def integralEquiv : Q ≃ₗ⁅ℤ⁆ P := LieEquiv.ofBijective integralToP integralToP_bijective

instance integral_free : Module.Free ℤ Q := integral_freeLie_submodule_free (Fin 2) _
instance P_free : Module.Free ℤ P := Module.Free.of_equiv integralEquiv.toLinearEquiv

theorem P_residuallyNilpotent : ResiduallyNilpotent ℤ P :=
  residuallyNilpotent_of_injective
    (integralAlgebra.incl.comp integralEquiv.symm.toLieHom)
    (Subtype.val_injective.comp integralEquiv.symm.injective)
    (freeLie_residuallyNilpotent (Fin 2))

end Parafree.TheoremB
