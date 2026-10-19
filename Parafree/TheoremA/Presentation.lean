import Parafree.TheoremA.Equations
import Mathlib.Algebra.Lie.Free

/-! The exact six-generator, three-relator Lie ring in Theorem A. -/

namespace Parafree.TheoremA

open Parafree.Lie

noncomputable section

abbrev PresentationFree := FreeLieAlgebra ℤ (Fin 3 ⊕ Fin 3)

def presentationX (i : Fin 3) : PresentationFree := FreeLieAlgebra.of ℤ (Sum.inl i)
def presentationQ (i : Fin 3) : PresentationFree := FreeLieAlgebra.of ℤ (Sum.inr i)

def relator (i : Fin 3) : PresentationFree :=
  presentationX i - equationStep presentationQ presentationX i

def relationIdeal : LieIdeal ℤ PresentationFree :=
  LieSubmodule.lieSpan ℤ PresentationFree (Set.range relator)

/-- The Lie ring with exactly the presentation in the manuscript. -/
abbrev K := PresentationFree ⧸ relationIdeal

namespace K

def x (i : Fin 3) : K := quotientMk relationIdeal (presentationX i)
def q (i : Fin 3) : K := quotientMk relationIdeal (presentationQ i)

theorem equations : equationStep q x = x := by
  funext i
  have hr : quotientMk relationIdeal (relator i) = 0 :=
    (quotientMk_eq_zero _ _).mpr (LieSubmodule.subset_lieSpan (Set.mem_range_self i))
  have he := congrFun (equationStep_map (quotientMk relationIdeal) presentationQ presentationX) i
  dsimp [relator] at hr
  rw [map_sub] at hr
  exact he.symm.trans (sub_eq_zero.mp hr).symm

theorem relation_z : x 0 = ⁅x 1, x 2⁆ + 2 • q 0 :=
  (congrFun equations 0).symm

theorem relation_u : x 1 = ⁅x 2, x 0⁆ + 2 • q 1 :=
  (congrFun equations 1).symm

theorem relation_v : x 2 = 2 • q 2 - ⁅x 0, x 1⁆ :=
  (congrFun equations 2).symm

variable {M : Type*} [LieRing M]

def freeLift (q' x' : Fin 3 → M) : PresentationFree →ₗ⁅ℤ⁆ M :=
  FreeLieAlgebra.lift ℤ (Sum.elim x' q')

@[simp] theorem freeLift_x (q' x' : Fin 3 → M) (i : Fin 3) :
    freeLift q' x' (presentationX i) = x' i :=
  FreeLieAlgebra.lift_of_apply (Sum.elim x' q') (Sum.inl i)

@[simp] theorem freeLift_q (q' x' : Fin 3 → M) (i : Fin 3) :
    freeLift q' x' (presentationQ i) = q' i :=
  FreeLieAlgebra.lift_of_apply (Sum.elim x' q') (Sum.inr i)

theorem freeLift_relator (q' x' : Fin 3 → M) (i : Fin 3) :
    freeLift q' x' (relator i) = x' i - equationStep q' x' i := by
  rw [relator, map_sub, freeLift_x]
  have he := congrFun (equationStep_map (freeLift q' x') presentationQ presentationX) i
  simpa only [freeLift_x, freeLift_q] using congrArg (fun t => x' i - t) he

def lift (q' x' : Fin 3 → M) (h : equationStep q' x' = x') : K →ₗ⁅ℤ⁆ M :=
  quotientLift relationIdeal (freeLift q' x') (by
    apply LieSubmodule.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    change freeLift q' x' (relator i) = 0
    rw [freeLift_relator, h, sub_self])

@[simp] theorem lift_x (q' x' : Fin 3 → M) (h : equationStep q' x' = x') (i : Fin 3) :
    lift q' x' h (x i) = x' i := freeLift_x q' x' i

@[simp] theorem lift_q (q' x' : Fin 3 → M) (h : equationStep q' x' = x') (i : Fin 3) :
    lift q' x' h (q i) = q' i := freeLift_q q' x' i

theorem hom_ext {f g : K →ₗ⁅ℤ⁆ M}
    (hx : ∀ i, f (x i) = g (x i)) (hq : ∀ i, f (q i) = g (q i)) : f = g := by
  apply quotient_hom_ext
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i with
  | inl i => exact hx i
  | inr i => exact hq i

theorem map_equations (f : K →ₗ⁅ℤ⁆ M) :
    equationStep (fun i => f (q i)) (fun i => f (x i)) = fun i => f (x i) := by
  rw [← equationStep_map, equations]

/-- Into a nilpotent target, the images of the three `q` generators determine the map. -/
theorem hom_ext_nilpotent (n : ℕ) (hn : lowerCentral ℤ M n = ⊥)
    {f g : K →ₗ⁅ℤ⁆ M} (hq : ∀ i, f (q i) = g (q i)) : f = g := by
  have hq' : (fun i => f (q i)) = fun i => g (q i) := funext hq
  have hx := solution_unique (fun i => g (q i)) n hn
    (hq' ▸ map_equations f) (map_equations g)
  exact hom_ext (congrFun hx) hq

end K

/-- The residual quotient in the statement of Theorem A. -/
abbrev L := K ⧸ residualIdeal ℤ K

def toL : K →ₗ⁅ℤ⁆ L := quotientMk (residualIdeal ℤ K)

def freeToK : FreeLieAlgebra ℤ (Fin 3) →ₗ⁅ℤ⁆ K := FreeLieAlgebra.lift ℤ K.q

/-- The specified map sends the three free generators to the three `q` classes. -/
def freeToL : FreeLieAlgebra ℤ (Fin 3) →ₗ⁅ℤ⁆ L := toL.comp freeToK

@[simp] theorem freeToK_of (i : Fin 3) : freeToK (FreeLieAlgebra.of ℤ i) = K.q i :=
  FreeLieAlgebra.lift_of_apply K.q i

@[simp] theorem freeToL_of (i : Fin 3) : freeToL (FreeLieAlgebra.of ℤ i) = toL (K.q i) := by
  simp [freeToL]

end
end Parafree.TheoremA
