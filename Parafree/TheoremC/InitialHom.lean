import Parafree.TheoremC.Presentation
import Parafree.Associative.UnitElimination

/-! Maps from the original two-relator algebra into nilpotent targets are
uniquely determined by the first four generator images. -/
noncomputable section
namespace Parafree.TheoremC
open Parafree.Associative
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]

theorem initialHom_relations (f : A₀ k →ₐ[k] B) :
    (1 + f (generator₀ k 0)) * (1 + f (generator₀ k 2)) =
      (1 + f (generator₀ k 3)) * (1 + f (generator₀ k 5)) ∧
    (1 + f (generator₀ k 0)) * (1 + f (generator₀ k 1)) * (1 + f (generator₀ k 2)) =
      (1 + f (generator₀ k 3)) * (1 + f (generator₀ k 4)) * (1 + f (generator₀ k 5)) := by
  constructor
  · apply sub_eq_zero.mp
    simpa [relator, generator₀, map_sub, map_mul, map_add, map_pow] using
      congrArg f (initial_relator k (0 : Fin 2))
  · apply sub_eq_zero.mp
    simpa [relator, generator₀, map_sub, map_mul, map_add, map_pow] using
      congrArg f (initial_relator k (1 : Fin 2))

theorem initialHom_ext {f g : A₀ k →ₐ[k] B}
    (h : ∀ i : Fin 6, f (generator₀ k i) = g (generator₀ k i)) : f = g := by
  apply Ideal.Quotient.algHom_ext k
  apply FreeAlgebra.hom_ext
  funext i
  exact h i

theorem initialHom_ext_four {f g : A₀ k →ₐ[k] B}
    (h : ∀ i : Fin 4, f (generator₀ k i.castSucc.castSucc) = g (generator₀ k i.castSucc.castSucc))
    (ha : IsUnit (1 + g (generator₀ k 0)))
    (hc : IsUnit (1 + g (generator₀ k 2)))
    (hd : IsUnit (1 + g (generator₀ k 3))) : f = g := by
  have h0 : f (generator₀ k 0) = g (generator₀ k 0) := h 0
  have h1 : f (generator₀ k 1) = g (generator₀ k 1) := h 1
  have h2 : f (generator₀ k 2) = g (generator₀ k 2) := h 2
  have h3 : f (generator₀ k 3) = g (generator₀ k 3) := h 3
  obtain ⟨a,ha⟩ := ha
  obtain ⟨c,hc⟩ := hc
  obtain ⟨d,hd⟩ := hd
  have hf := initialHom_relations f
  have hg := initialHom_relations g
  rw [h0,h1,h2,h3,← ha,← hc,← hd] at hf
  rw [← ha,← hc,← hd] at hg
  have ef := solution_unique a c d (1 + g (generator₀ k 1))
    (1 + f (generator₀ k 4)) (1 + f (generator₀ k 5)) hf.1 hf.2
  have eg := solution_unique a c d (1 + g (generator₀ k 1))
    (1 + g (generator₀ k 4)) (1 + g (generator₀ k 5)) hg.1 hg.2
  apply initialHom_ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact add_left_cancel (ef.1.trans eg.1.symm)
  · exact add_left_cancel (ef.2.trans eg.2.symm)

end Parafree.TheoremC
