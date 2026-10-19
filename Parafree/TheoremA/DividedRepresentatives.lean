import Parafree.TheoremA.DividedFiltration
import Parafree.TheoremA.RationalModel
import Parafree.Linear.DividedSum

/-! The divided-sum injectivity criterion for the actual integral relation
filtration inside its faithful rational ambient free Lie algebra. -/

noncomputable section
namespace Parafree.TheoremA.Auxiliary

open Parafree.Linear.DividedFiltration

/-- Evaluate a finite family using precisely the halves of the original relations. -/
def dividedValue (x : ℕ →₀ Free ℤ) : RationalModel.Ambient :=
  finiteSum RationalModel.integralInclusion.toLinearMap (1 / 2 : ℚ) x

/-- A divided representative can be twice another divided representative only
if each coefficient vanishes in the corresponding graded reduction.
The two representatives may have different finite denominator bounds. -/
theorem dividedValue_even_coefficients (x y : ℕ →₀ Free ℤ)
    (hx : ∀ j, x j ∈ dividedFiltration j) (hy : ∀ j, y j ∈ dividedFiltration j)
    (h : dividedValue x = (2 : ℤ) • dividedValue y) (j : ℕ) :
    ∃ a ∈ dividedFiltration (j + 1), ∃ b ∈ dividedFiltration j,
      x j = a + (2 : ℤ) • b :=
  term_decomposition_of_finiteSum dividedFiltration dividedFiltration_antitone
    (2 : ℤ) (dividedFiltration_saturated 2 (by decide))
    RationalModel.integralInclusion.toLinearMap RationalModel.integralInclusion_injective
    (1 / 2 : ℚ) (by norm_num) x y hx hy h j

end Parafree.TheoremA.Auxiliary
