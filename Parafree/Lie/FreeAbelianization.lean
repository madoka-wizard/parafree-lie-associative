import Parafree.Lie.LowerCentral
import Mathlib.Algebra.Lie.Free

/-! Explicit abelianization of a free integral Lie ring of any finite rank. -/

noncomputable section
namespace Parafree.Lie.FreeAbelianization

open scoped BigOperators

abbrev Coordinates (n : ℕ) := Fin n → ℤ
abbrev Free (n : ℕ) := FreeLieAlgebra ℤ (Fin n)
abbrev Quotient (n : ℕ) := Free n ⧸ lowerCentral ℤ (Free n) 1

def generator (n : ℕ) (i : Fin n) : Quotient n := quotientMk _ (FreeLieAlgebra.of ℤ i)

variable (n : ℕ)

theorem coordinates_lie_zero (x y : Coordinates n) : ⁅x, y⁆ = 0 := by
  simp [LieRing.of_associative_ring_bracket, mul_comm]

theorem coordinates_lowerCentral_one : lowerCentral ℤ (Coordinates n) 1 = ⊥ := by
  apply le_antisymm _ bot_le
  simp only [lowerCentral, LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
  rw [LieSubmodule.lie_le_iff]
  intro x _ y _
  simpa only [coordinates_lie_zero] using (LieSubmodule.zero_mem (⊥ : LieIdeal ℤ (Coordinates n)))

def freeCoordinates : Free n →ₗ⁅ℤ⁆ Coordinates n :=
  FreeLieAlgebra.lift ℤ (fun i => Pi.single i 1)

def coordinates : Quotient n →ₗ⁅ℤ⁆ Coordinates n :=
  quotientLift _ (freeCoordinates n) (lowerCentral_le_ker _ 1 (coordinates_lowerCentral_one n))

@[simp] theorem coordinates_generator (i : Fin n) :
    coordinates n (generator n i) = Pi.single i 1 := FreeLieAlgebra.lift_of_apply _ i

def sectionMap : Coordinates n →ₗ⁅ℤ⁆ Quotient n where
  toFun x := ∑ i, x i • generator n i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum, mul_smul]
  map_lie' {x y} := by
    rw [coordinates_lie_zero]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (lie_eq_zero_of_lowerCentral_one (lowerCentral_quotient_eq_bot 1) _ _).symm

@[simp] theorem sectionMap_single (i : Fin n) :
    sectionMap n (Pi.single i 1) = generator n i := by
  simp [sectionMap, Pi.single_apply]

theorem sectionMap_left : (sectionMap n).comp (coordinates n) = LieHom.id := by
  apply quotient_hom_ext
  apply FreeLieAlgebra.hom_ext
  intro i
  change sectionMap n (coordinates n (generator n i)) = generator n i
  rw [coordinates_generator, sectionMap_single]

theorem sectionMap_right : (coordinates n).comp (sectionMap n) = LieHom.id := by
  apply LieHom.ext
  intro x
  change coordinates n (∑ i, x i • generator n i) = x
  simp only [map_sum, map_smul, coordinates_generator]
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

def equiv : Quotient n ≃ₗ⁅ℤ⁆ Coordinates n :=
  LieEquiv.ofBijective (coordinates n)
    ⟨Function.LeftInverse.injective
      (show Function.LeftInverse (sectionMap n) (coordinates n) from
        fun x => DFunLike.congr_fun (sectionMap_left n) x),
      Function.RightInverse.surjective
      (show Function.RightInverse (sectionMap n) (coordinates n) from
        fun x => DFunLike.congr_fun (sectionMap_right n) x)⟩

end Parafree.Lie.FreeAbelianization
