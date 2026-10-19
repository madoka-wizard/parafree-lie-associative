import Parafree.TheoremA.Parafree
import LieRings.Homological.LieHomology.LowDegreeHomology

/-! Integral abelianization and first CE homology of the actual ring in Theorem A. -/

namespace Parafree.TheoremA

open Parafree.Lie
open scoped BigOperators

noncomputable section

/-- The coordinate module uses the zero commutator bracket of its commutative ring. -/
abbrev AbelianCoordinates := Fin 3 → ℤ

theorem coordinates_lie_zero (x y : AbelianCoordinates) : ⁅x, y⁆ = 0 := by
  simp [LieRing.of_associative_ring_bracket, mul_comm]

theorem coordinates_lowerCentral_one : lowerCentral ℤ AbelianCoordinates 1 = ⊥ := by
  apply le_antisymm _ bot_le
  simp only [lowerCentral, LieModule.lowerCentralSeries_succ,
    LieModule.lowerCentralSeries_zero]
  rw [LieSubmodule.lie_le_iff]
  intro x _ y _
  simpa only [coordinates_lie_zero] using (LieSubmodule.zero_mem (⊥ : LieIdeal ℤ AbelianCoordinates))

def freeCoordinates : FreeThree →ₗ⁅ℤ⁆ AbelianCoordinates :=
  FreeLieAlgebra.lift ℤ (fun i => Pi.single i 1)

def abelianCoordinates : FreeNilpotent 1 →ₗ⁅ℤ⁆ AbelianCoordinates :=
  quotientLift _ freeCoordinates (lowerCentral_le_ker _ 1 coordinates_lowerCentral_one)

@[simp] theorem abelianCoordinates_gen (i : Fin 3) :
    abelianCoordinates (nilpotentGenerators 1 i) = Pi.single i 1 :=
  FreeLieAlgebra.lift_of_apply _ i

def abelianSection : AbelianCoordinates →ₗ⁅ℤ⁆ FreeNilpotent 1 where
  toFun x := ∑ i, x i • nilpotentGenerators 1 i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum, mul_smul]
  map_lie' {x y} := by
    rw [coordinates_lie_zero]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (lie_eq_zero_of_lowerCentral_one (lowerCentral_quotient_eq_bot 1) _ _).symm

@[simp] theorem abelianSection_single (i : Fin 3) :
    abelianSection (Pi.single i 1) = nilpotentGenerators 1 i := by
  simp [abelianSection, Pi.single_apply]

theorem abelianSection_left : abelianSection.comp abelianCoordinates = LieHom.id := by
  apply quotient_hom_ext
  apply FreeLieAlgebra.hom_ext
  intro i
  change abelianSection (abelianCoordinates (nilpotentGenerators 1 i)) = nilpotentGenerators 1 i
  rw [abelianCoordinates_gen, abelianSection_single]

theorem abelianSection_right : abelianCoordinates.comp abelianSection = LieHom.id := by
  apply LieHom.ext
  intro x
  change abelianCoordinates (∑ i, x i • nilpotentGenerators 1 i) = x
  simp only [map_sum, map_smul, abelianCoordinates_gen]
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

def freeAbelianizationEquiv : FreeNilpotent 1 ≃ₗ⁅ℤ⁆ AbelianCoordinates :=
  LieEquiv.ofBijective abelianCoordinates
    ⟨Function.LeftInverse.injective
      (show Function.LeftInverse abelianSection abelianCoordinates from
        fun x => DFunLike.congr_fun abelianSection_left x),
      Function.RightInverse.surjective
      (show Function.RightInverse abelianSection abelianCoordinates from
        fun x => DFunLike.congr_fun abelianSection_right x)⟩

/-- The abelianization of `L` is a free integral module of rank three. -/
def L_abelianizationEquiv : (L ⧸ lowerCentral ℤ L 1) ≃ₗ⁅ℤ⁆ AbelianCoordinates :=
  (LieEquiv.ofBijective (nilpotentMap freeToL 1) (freeToL_isParaEquivalence 1)).symm.trans
    freeAbelianizationEquiv

instance L_abelianization_isTorsionFree : Module.IsTorsionFree ℤ (L ⧸ lowerCentral ℤ L 1) :=
  Function.Injective.moduleIsTorsionFree (R := ℤ)
    L_abelianizationEquiv L_abelianizationEquiv.injective
    (fun r x => L_abelianizationEquiv.toLinearEquiv.map_smul r x)

open LieRings.Homological.LieHomology

/-- This is the actual CE first homology, needed for reduction modulo two. -/
def L_homologyOneEquiv : Homology (R := ℤ) (L := L) 1 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (homologyOneEquivAbelianization ℤ L).trans (by
    simpa only [lowerCentral, LieModule.lowerCentralSeries_succ,
      LieModule.lowerCentralSeries_zero] using L_abelianizationEquiv.toLinearEquiv)

theorem L_homologyOne_two_smul_injective :
    Function.Injective (fun x : Homology (R := ℤ) (L := L) 1 => (2 : ℤ) • x) := by
  intro x y h
  change (2 : ℤ) • x = (2 : ℤ) • y at h
  apply L_homologyOneEquiv.injective
  rw [show (2 : ℤ) • x = x + x from two_zsmul x,
    show (2 : ℤ) • y = y + y from two_zsmul y] at h
  have he := congrArg L_homologyOneEquiv h
  simp only [map_add] at he
  funext i
  have hi := congrFun he i
  change L_homologyOneEquiv x i + L_homologyOneEquiv x i =
    L_homologyOneEquiv y i + L_homologyOneEquiv y i at hi
  omega

end
end Parafree.TheoremA
