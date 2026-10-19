import Parafree.TheoremC.Separated
import Parafree.TheoremC.ParaEquivalence
import Parafree.TheoremC.SecondHomology
import Parafree.TheoremC.FinitePresentation

/-! Theorem C of the current manuscript, for every nonzero commutative
coefficient ring. The homology is actual derived coinvariants. -/
noncomputable section
namespace Parafree.TheoremC
open Parafree.Associative
variable (k : Type*) [CommRing k] [Nontrivial k]

/-- Parafreeness via the specified four generators, the second Tor module,
and finite generation without finite presentation of the literal quotient. -/
theorem theoremC :
    ResiduallyNilpotent (augmentation k) ∧
    (augmentedFourToFull k).IsParaEquivalence ∧
    Nonempty (homology k 2 ≃ₗ[k] (ℕ →₀ k)) ∧
    Function.Surjective (toFull k) ∧ ¬ IsFinitelyPresented k (A k) :=
  ⟨fullQuotient_residuallyNilpotent k, fourToFull_isParaEquivalence k,
    ⟨homologyTwoEquiv k⟩, Ideal.Quotient.mkₐ_surjective k (fullIdeal k),
    not_finitelyPresented k⟩

end Parafree.TheoremC
