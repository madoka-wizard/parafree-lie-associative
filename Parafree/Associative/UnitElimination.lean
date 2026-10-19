import Parafree.Associative.UnitRelations

/-! Explicit elimination and uniqueness for the two associative relations. -/
noncomputable section
namespace Parafree.Associative
variable {A : Type*} [Ring A]

def solvedX (a d : Aˣ) (b : A) : A := (↑(d⁻¹) : A) * a * b * ↑(a⁻¹) * d
def solvedY (a d : Aˣ) (c : A) : A := (↑(d⁻¹) : A) * a * c

theorem solved_zero (a d : Aˣ) (c : A) : (a : A) * c = d * solvedY a d c := by
  simp [solvedY, mul_assoc]

theorem solved_one (a d : Aˣ) (b c : A) :
    (a : A) * b * c = d * solvedX a d b * solvedY a d c := by
  simp [solvedX, solvedY, mul_assoc]

theorem solution_unique (a c d : Aˣ) (b x y : A)
    (h₀ : (a : A) * c = d * y) (h₁ : (a : A) * b * c = d * x * y) :
    x = solvedX a d b ∧ y = solvedY a d c := by
  have hy : y = solvedY a d c := by
    have h := congrArg (fun z : A => (↑(d⁻¹) : A) * z) h₀
    simpa [solvedY, mul_assoc] using h.symm
  refine ⟨?_,hy⟩
  have h := congrArg (fun z : A => (↑(d⁻¹) : A) * z * ↑(c⁻¹) * ↑(a⁻¹) * d) h₁
  simpa [hy, solvedX, solvedY, mul_assoc] using h.symm

end Parafree.Associative
