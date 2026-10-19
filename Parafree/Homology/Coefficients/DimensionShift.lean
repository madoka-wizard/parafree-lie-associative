import Parafree.Homology.Coefficients.ExactSequence
import Parafree.Homology.Coefficients.Trivial

/-! Composition of two connecting isomorphisms, including comparison to upstream
trivial-coefficient homology. Exactness and the four necessary vanishing statements
are explicit inputs; this file does not assert vanishing for enveloping modules. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Parafree.Homology.Coefficients

universe u v w
variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {W P I Q T : Type w}
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]
  [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]
  [AddCommGroup I] [Module R I] [LieRingModule L I] [LieModule R L I]
  [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]
  [AddCommGroup T] [Module R T] [LieRingModule L T] [LieModule R L T]

/-- Two dimension shifts for `0 → W → P → I → 0` and `0 → I → Q → T → 0`. -/
def doubleDimensionShift
    {f : W →ₗ⁅R,L⁆ P} {g : P →ₗ⁅R,L⁆ I} {hfg : g.comp f = 0}
    {a : I →ₗ⁅R,L⁆ Q} {b : Q →ₗ⁅R,L⁆ T} {hab : b.comp a = 0}
    (h₁ : (sequence f g hfg).ShortExact) (h₂ : (sequence a b hab).ShortExact) (n : ℕ)
    (hP₁ : IsZero (homology R L P (n + 1))) (hP₀ : IsZero (homology R L P n))
    (hQ₂ : IsZero (homology R L Q (n + 2))) (hQ₁ : IsZero (homology R L Q (n + 1))) :
    Homology R L W n ≃ₗ[R] Homology R L T (n + 2) :=
  (dimensionShift h₁ n hP₁ hP₀).symm.trans (dimensionShift h₂ (n + 1) hQ₂ hQ₁).symm

section Scalars

variable {W' P' I' Q' : Type u}
  [AddCommGroup W'] [Module R W'] [LieRingModule L W'] [LieModule R L W']
  [AddCommGroup P'] [Module R P'] [LieRingModule L P'] [LieModule R L P']
  [AddCommGroup I'] [Module R I'] [LieRingModule L I'] [LieModule R L I']
  [AddCommGroup Q'] [Module R Q'] [LieRingModule L Q'] [LieModule R L Q']

/-- The form needed for a two-step resolution of the trivial module. -/
def doubleDimensionShiftTrivial
    {f : W' →ₗ⁅R,L⁆ P'} {g : P' →ₗ⁅R,L⁆ I'} {hfg : g.comp f = 0}
    {a : I' →ₗ⁅R,L⁆ Q'} {b : Q' →ₗ⁅R,L⁆ Trivial R L} {hab : b.comp a = 0}
    (h₁ : (sequence f g hfg).ShortExact) (h₂ : (sequence a b hab).ShortExact) (n : ℕ)
    (hP₁ : IsZero (homology R L P' (n + 1))) (hP₀ : IsZero (homology R L P' n))
    (hQ₂ : IsZero (homology R L Q' (n + 2))) (hQ₁ : IsZero (homology R L Q' (n + 1))) :
    Homology R L W' n ≃ₗ[R]
      LieRings.Homological.LieHomology.Homology (R := R) (L := L) (n + 2) :=
  (doubleDimensionShift h₁ h₂ n hP₁ hP₀ hQ₂ hQ₁).trans (trivialHomologyEquiv R L (n + 2))

end Scalars
end Parafree.Homology.Coefficients
