import Parafree.TheoremA.Presentation
import Parafree.Lie.Parafree

/-!
# Theorem A, part (1)

The proof uses finite iteration of the presentation equations. It constructs inverse
maps on every lower-central quotient and then passes to the residual quotient.
-/

namespace Parafree.TheoremA

open Parafree.Lie

noncomputable section

abbrev FreeThree := FreeLieAlgebra ℤ (Fin 3)
abbrev FreeNilpotent (n : ℕ) := FreeThree ⧸ lowerCentral ℤ FreeThree n
abbrev KNilpotent (n : ℕ) := K ⧸ lowerCentral ℤ K n

def nilpotentGenerators (n : ℕ) (i : Fin 3) : FreeNilpotent n :=
  quotientMk _ (FreeLieAlgebra.of ℤ i)

def solvePresentation (n : ℕ) : K →ₗ⁅ℤ⁆ FreeNilpotent n :=
  K.lift (nilpotentGenerators n) (nilpotentSolution (nilpotentGenerators n) n)
    (nilpotentSolution_isFixed _ n (lowerCentral_quotient_eq_bot n))

@[simp] theorem solvePresentation_q (n : ℕ) (i : Fin 3) :
    solvePresentation n (K.q i) = nilpotentGenerators n i := K.lift_q _ _ _ i

def nilpotentInverse (n : ℕ) : KNilpotent n →ₗ⁅ℤ⁆ FreeNilpotent n :=
  quotientLift _ (solvePresentation n)
    (lowerCentral_le_ker _ n (lowerCentral_quotient_eq_bot n))

@[simp] theorem nilpotentInverse_mk (n : ℕ) (x : K) :
    nilpotentInverse n (quotientMk _ x) = solvePresentation n x := rfl

theorem nilpotentInverse_left (n : ℕ) :
    (nilpotentInverse n).comp (nilpotentMap freeToK n) = LieHom.id := by
  apply quotient_hom_ext
  apply FreeLieAlgebra.hom_ext
  intro i
  change nilpotentInverse n (nilpotentMap freeToK n
    (quotientMk _ (FreeLieAlgebra.of ℤ i))) = quotientMk _ (FreeLieAlgebra.of ℤ i)
  simp only [nilpotentMap_mk, freeToK_of, nilpotentInverse_mk, solvePresentation_q]
  rfl

theorem nilpotentInverse_right (n : ℕ) :
    (nilpotentMap freeToK n).comp (nilpotentInverse n) = LieHom.id := by
  apply quotient_hom_ext
  apply K.hom_ext_nilpotent n (lowerCentral_quotient_eq_bot n)
  intro i
  change nilpotentMap freeToK n (nilpotentInverse n (quotientMk _ (K.q i))) =
    quotientMk _ (K.q i)
  rw [nilpotentInverse_mk, solvePresentation_q]
  change nilpotentMap freeToK n (quotientMk _ (FreeLieAlgebra.of ℤ i)) = _
  rw [nilpotentMap_mk, freeToK_of]

theorem freeToK_isParaEquivalence : IsParaEquivalence freeToK := by
  intro n
  exact ⟨Function.LeftInverse.injective
    (fun x => DFunLike.congr_fun (nilpotentInverse_left n) x),
    Function.RightInverse.surjective
    (fun x => DFunLike.congr_fun (nilpotentInverse_right n) x)⟩

/-- Explicit isomorphism on the quotient by the manuscript's `gamma_(n+1)`. -/
def nilpotentEquiv (n : ℕ) : FreeNilpotent n ≃ₗ⁅ℤ⁆ KNilpotent n :=
  LieEquiv.ofBijective (nilpotentMap freeToK n) (freeToK_isParaEquivalence n)

theorem L_residuallyNilpotent : ResiduallyNilpotent ℤ L :=
  residualQuotient_residuallyNilpotent

theorem freeToL_isParaEquivalence : IsParaEquivalence freeToL :=
  IsParaEquivalence.comp residualQuotient_isParaEquivalence freeToK_isParaEquivalence

/-- The complete first numbered assertion of Theorem A, including its specified map. -/
theorem theoremA_part_one : IsParafree L 3 ∧ IsParaEquivalence freeToL :=
  ⟨⟨L_residuallyNilpotent, freeToL, freeToL_isParaEquivalence⟩,
    freeToL_isParaEquivalence⟩

end
end Parafree.TheoremA
