import Parafree.TheoremA.Parafree
import Parafree.Lie.FreeResidual

/-!
# An integral realization of the residual quotient

Dilating the rational realization by sending each ambient generator to twice itself
replaces its six generators by `2z, 2u, 2v, z-2[u,v], u-2[v,z], v+2[z,u]`.
We construct this model directly inside the integral free Lie ring. The equality of
its presentation kernel with the residual ideal is proved using finite iteration.
-/

namespace Parafree.TheoremA

open Parafree.Lie

noncomputable section

section Equations

variable {M : Type*} [LieRing M]

def quadratic (x : Fin 3 → M) : Fin 3 → M :=
  ![⁅x 1, x 2⁆, ⁅x 2, x 0⁆, -⁅x 0, x 1⁆]

def correction (x : Fin 3 → M) (i : Fin 3) : M := x i - (2 : ℤ) • quadratic x i

def inverseStep (q x : Fin 3 → M) (i : Fin 3) : M := q i + (2 : ℤ) • quadratic x i

theorem inverseStep_contracting (q : Fin 3 → M) :
    FiltrationContracting ℤ (inverseStep q) := by
  intro n x y h i
  have hb : quadratic x i - quadratic y i ∈ lowerCentral ℤ M (n + 1) := by
    fin_cases i
    · exact lie_sub_lie_mem_lowerCentral_succ n (h 1) (h 2)
    · exact lie_sub_lie_mem_lowerCentral_succ n (h 2) (h 0)
    · change -⁅x 0, x 1⁆ - -⁅y 0, y 1⁆ ∈ lowerCentral ℤ M (n + 1)
      simpa only [neg_sub_neg, neg_sub] using (lowerCentral ℤ M (n + 1)).neg_mem
        (lie_sub_lie_mem_lowerCentral_succ n (h 0) (h 1))
  simpa [inverseStep, smul_sub] using (lowerCentral ℤ M (n + 1)).smul_mem (2 : ℤ) hb

theorem correction_eq_of_fixed {q x : Fin 3 → M} (h : inverseStep q x = x) :
    correction x = q := by
  funext i
  have hi := congrFun h i
  dsimp [inverseStep] at hi
  dsimp [correction]
  rw [← hi, add_sub_cancel_right]

theorem correction_map {N : Type*} [LieRing N] (f : M →ₗ⁅ℤ⁆ N) (x : Fin 3 → M) :
    (fun i => f (correction x i)) = correction (fun i => f (x i)) := by
  funext i
  fin_cases i <;> simp [correction, quadratic, LieHom.map_lie]

end Equations

def integralX (i : Fin 3) : FreeThree := (2 : ℤ) • FreeLieAlgebra.of ℤ i
def integralQ : Fin 3 → FreeThree := correction (FreeLieAlgebra.of ℤ)

theorem integral_equations : equationStep integralQ integralX = integralX := by
  funext i
  let g := FreeLieAlgebra.of ℤ (X := Fin 3)
  fin_cases i
  · change ⁅(2 : ℤ) • g 1, (2 : ℤ) • g 2⁆ +
      2 • (g 0 - (2 : ℤ) • ⁅g 1, g 2⁆) = (2 : ℤ) • g 0
    simp only [smul_lie, lie_smul]
    module
  · change ⁅(2 : ℤ) • g 2, (2 : ℤ) • g 0⁆ +
      2 • (g 1 - (2 : ℤ) • ⁅g 2, g 0⁆) = (2 : ℤ) • g 1
    simp only [smul_lie, lie_smul]
    module
  · change 2 • (g 2 - (2 : ℤ) • (-⁅g 0, g 1⁆)) -
      ⁅(2 : ℤ) • g 0, (2 : ℤ) • g 1⁆ = (2 : ℤ) • g 2
    simp only [smul_lie, lie_smul]
    module

def integralEvaluation : K →ₗ⁅ℤ⁆ FreeThree := K.lift integralQ integralX integral_equations

@[simp] theorem integralEvaluation_x (i : Fin 3) : integralEvaluation (K.x i) = integralX i :=
  K.lift_x _ _ _ i

@[simp] theorem integralEvaluation_q (i : Fin 3) : integralEvaluation (K.q i) = integralQ i :=
  K.lift_q _ _ _ i

def correctionInverse (n : ℕ) : FreeThree →ₗ⁅ℤ⁆ FreeNilpotent n :=
  FreeLieAlgebra.lift ℤ ((inverseStep (nilpotentGenerators n))^[n] 0)

theorem correctionInverse_q (n : ℕ) (i : Fin 3) :
    correctionInverse n (integralQ i) = nilpotentGenerators n i := by
  have hfixed := iterate_isFixed (inverseStep_contracting (nilpotentGenerators n)) n
    (lowerCentral_quotient_eq_bot n) 0
  have hc := congrFun (correction_eq_of_fixed hfixed) i
  have hm := congrFun (correction_map (correctionInverse n) (FreeLieAlgebra.of ℤ)) i
  have hgen (j : Fin 3) : correctionInverse n (FreeLieAlgebra.of ℤ j) =
      (inverseStep (nilpotentGenerators n))^[n] 0 j := FreeLieAlgebra.lift_of_apply _ j
  exact hm.trans (by simpa only [hgen] using hc)

theorem correctionInverse_comp (n : ℕ) :
    (correctionInverse n).comp integralEvaluation = solvePresentation n := by
  apply K.hom_ext_nilpotent n (lowerCentral_quotient_eq_bot n)
  intro i
  simp only [LieHom.comp_apply, integralEvaluation_q, correctionInverse_q, solvePresentation_q]

/-- The concrete map into the integral free ring has exactly the residual kernel. -/
theorem integralEvaluation_ker : integralEvaluation.ker = residualIdeal ℤ K := by
  apply le_antisymm
  · intro x hx
    change integralEvaluation x = 0 at hx
    rw [residualIdeal, LieSubmodule.mem_iInf]
    intro n
    apply (quotientMk_eq_zero _ _).mp
    have hs : solvePresentation n x = 0 := by
      rw [← correctionInverse_comp]
      change correctionInverse n (integralEvaluation x) = 0
      rw [hx, map_zero]
    have hid := DFunLike.congr_fun (nilpotentInverse_right n) (quotientMk (lowerCentral ℤ K n) x)
    change nilpotentMap freeToK n (nilpotentInverse n (quotientMk _ x)) = quotientMk _ x at hid
    rw [nilpotentInverse_mk, hs, map_zero] at hid
    exact hid.symm
  · intro x hx
    change integralEvaluation x = 0
    have hm : integralEvaluation x ∈ residualIdeal ℤ FreeThree := by
      rw [residualIdeal, LieSubmodule.mem_iInf]
      intro n
      exact map_mem_lowerCentral integralEvaluation n ((residualIdeal_le n) hx)
    simpa only [show residualIdeal ℤ FreeThree = ⊥ from freeLie_residuallyNilpotent (Fin 3),
      LieSubmodule.mem_bot] using hm

def integralRealization : L →ₗ⁅ℤ⁆ FreeThree :=
  quotientLift _ integralEvaluation (by rw [integralEvaluation_ker])

@[simp] theorem integralRealization_toL (x : K) :
    integralRealization (toL x) = integralEvaluation x := rfl

theorem integralRealization_injective : Function.Injective integralRealization := by
  intro x y h
  obtain ⟨x, rfl⟩ := quotientMk_surjective (residualIdeal ℤ K) x
  obtain ⟨y, rfl⟩ := quotientMk_surjective (residualIdeal ℤ K) y
  apply sub_eq_zero.mp
  rw [← map_sub, quotientMk_eq_zero, ← integralEvaluation_ker]
  change integralEvaluation (x - y) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr h

/-- A faithful integral model, obtained as a Lie subring of the integral free Lie ring. -/
def integralModelEquiv : L ≃ₗ⁅ℤ⁆ integralRealization.range :=
  integralRealization.equivRangeOfInjective integralRealization_injective

def associativeRealization : L →ₗ⁅ℤ⁆ FreeAlgebra ℤ (Fin 3) :=
  (LieRings.PBW.freeLieToFreeAlgebra ℤ (Fin 3)).comp integralRealization

theorem associativeRealization_injective : Function.Injective associativeRealization :=
  (LieRings.FreeLieDimension.freeLieToFreeAlgebra_injective_int (Fin 3)).comp
    integralRealization_injective

instance L_isTorsionFree : Module.IsTorsionFree ℤ L := by
  letI : Module.IsTorsionFree ℤ (FreeAlgebra ℤ (Fin 3)) :=
    (FreeAlgebra.basisFreeMonoid ℤ (Fin 3)).isTorsionFree
  exact Function.Injective.moduleIsTorsionFree (R := ℤ)
    associativeRealization associativeRealization_injective
    (fun r x => map_smul associativeRealization r x)

end
end Parafree.TheoremA
