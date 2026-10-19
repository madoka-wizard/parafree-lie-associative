import Parafree.Lie.NilpotentFixedPoint

/-! The three recursive presentation equations of Theorem A. -/

namespace Parafree.TheoremA

open Parafree.Lie

variable {L : Type*} [LieRing L]

/-- The coordinate order is `z, u, v`; the parameters are `q₁, q₂, q₃`. -/
def equationStep (q x : Fin 3 → L) : Fin 3 → L :=
  ![⁅x 1, x 2⁆ + 2 • q 0, ⁅x 2, x 0⁆ + 2 • q 1, 2 • q 2 - ⁅x 0, x 1⁆]

theorem equationStep_contracting (q : Fin 3 → L) :
    FiltrationContracting ℤ (equationStep q) := by
  intro n x y h i
  fin_cases i
  · simpa [equationStep] using lie_sub_lie_mem_lowerCentral_succ n (h 1) (h 2)
  · simpa [equationStep] using lie_sub_lie_mem_lowerCentral_succ n (h 2) (h 0)
  · have hneg := (lowerCentral ℤ L (n + 1)).neg_mem
      (lie_sub_lie_mem_lowerCentral_succ n (h 0) (h 1))
    simpa [equationStep] using hneg

theorem equationStep_map {M : Type*} [LieRing M] (f : L →ₗ⁅ℤ⁆ M)
    (q x : Fin 3 → L) :
    (fun i => f (equationStep q x i)) =
      equationStep (fun i => f (q i)) (fun i => f (x i)) := by
  funext i
  fin_cases i <;> simp [equationStep, LieHom.map_lie]

def nilpotentSolution (q : Fin 3 → L) (n : ℕ) : Fin 3 → L :=
  (equationStep q)^[n] 0

theorem nilpotentSolution_isFixed (q : Fin 3 → L) (n : ℕ)
    (hn : lowerCentral ℤ L n = ⊥) :
    equationStep q (nilpotentSolution q n) = nilpotentSolution q n :=
  iterate_isFixed (equationStep_contracting q) n hn 0

theorem solution_unique (q : Fin 3 → L) (n : ℕ) (hn : lowerCentral ℤ L n = ⊥)
    {x y : Fin 3 → L} (hx : equationStep q x = x) (hy : equationStep q y = y) :
    x = y := fixedPoint_unique (equationStep_contracting q) n hn hx hy

end Parafree.TheoremA
