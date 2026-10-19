import Parafree.Upstream.CE
import Parafree.Homology.ScalarReduction

/-! Uniform cycles, classes, and cocycle evaluations in every positive degree
of the actual Chevalley--Eilenberg complex. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.Homology.Concrete
open CategoryTheory LieRings.Homological.LieHomology
variable (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] (n : ℕ)

abbrev Cycles := LinearMap.ker (differential R L n)
def boundary : (⋀[R]^(n+2) L) →ₗ[R] Cycles R L n :=
  ScalarReduction.boundary (differential R L n) (differential R L (n+1))
    (differential_comp_differential R L n)
abbrev Quotient := Cycles R L n ⧸ LinearMap.range (boundary R L n)

-- Cache the canonical quotient instance instead of repeating the search through
-- the kernel/image presentation at each composition of linear maps.
local instance quotientAddCommMonoid : AddCommMonoid (Quotient R L n) :=
  (Submodule.Quotient.addCommGroup _).toAddCommMonoid

/-- Degree `n+1` of the library complex, with its ordinary kernel/image model. -/
def equiv : Homology (R := R) (L := L) (n+1) ≃ₗ[R] Quotient R L n := by
  let S := ShortComplex.moduleCatMk (differential R L (n+1)) (differential R L n)
    (differential_comp_differential R L n)
  have hs : (complex R L).sc' (n+2) (n+1) n = S := by
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
      complex_d, S, ShortComplex.moduleCatMk]
  let a := (complex R L).homologyIsoSc' (n+2) (n+1) n (by simp) (by simp)
  let b := eqToIso (congrArg (fun (s : ShortComplex (ModuleCat R)) => s.homology) hs)
  exact (a ≪≫ b ≪≫ S.moduleCatHomologyIso).toLinearEquiv

def homologyClass : Cycles R L n →ₗ[R] Homology (R := R) (L := L) (n+1) :=
  (equiv R L n).symm.toLinearMap.comp (LinearMap.range (boundary R L n)).mkQ

theorem homologyClass_eq_zero (z : Cycles R L n) :
    homologyClass R L n z = 0 ↔ ∃ b, differential R L (n+1) b = z.1 := by
  change (equiv R L n).symm ((LinearMap.range (boundary R L n)).mkQ z) = 0 ↔ _
  rw [← (equiv R L n).symm.map_zero, (equiv R L n).symm.injective.eq_iff]
  exact ScalarReduction.class_eq_zero _ _ _ z

variable {M : Type*} [AddCommGroup M] [Module R M]

def evaluate (f : (⋀[R]^(n+1) L) →ₗ[R] M)
    (hf : f.comp (differential R L (n+1)) = 0) :
    Homology (R := R) (L := L) (n+1) →ₗ[R] M :=
  ((LinearMap.range (boundary R L n)).liftQ (f.comp (Cycles R L n).subtype)
    (by
      rintro _ ⟨b,rfl⟩
      exact LinearMap.congr_fun hf b)).comp (equiv R L n).toLinearMap

@[simp] theorem evaluate_class (f : (⋀[R]^(n+1) L) →ₗ[R] M)
    (hf : f.comp (differential R L (n+1)) = 0) (z : Cycles R L n) :
    evaluate R L n f hf (homologyClass R L n z) = f z.1 := by
  simp only [evaluate, homologyClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, Submodule.liftQ_apply, Submodule.mkQ_apply,
    Submodule.subtype_apply]

end Parafree.Homology.Concrete
