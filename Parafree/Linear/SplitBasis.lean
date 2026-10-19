import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.Prod

/-! An adapted basis for a submodule with free submodule and free quotient.
The quotient section is only linear; no Lie splitting is assumed. -/

noncomputable section

namespace Parafree.Linear.SplitBasis

variable {R M ι κ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (P : Submodule R M) [Module.Free R (M ⧸ P)]

/-- Projectivity of the quotient supplies a linear section. -/
def sectionMap : (M ⧸ P) →ₗ[R] M :=
  Classical.choose (P.mkQ.exists_rightInverse_of_surjective P.range_mkQ)

@[simp] theorem mkQ_sectionMap (x : M ⧸ P) : P.mkQ (sectionMap P x) = x :=
  LinearMap.congr_fun
    (Classical.choose_spec (P.mkQ.exists_rightInverse_of_surjective P.range_mkQ)) x

/-- Decompose a module into its submodule and a lifted copy of its quotient. -/
def equiv : (P × (M ⧸ P)) ≃ₗ[R] M :=
  LinearEquiv.ofBijective (P.subtype.coprod (sectionMap P)) (by
    constructor
    · intro a b h
      have hab : a.2 = b.2 := by
        have hq := congrArg P.mkQ h
        change P.mkQ ((a.1 : M) + sectionMap P a.2) =
          P.mkQ ((b.1 : M) + sectionMap P b.2) at hq
        have hz (y : P) : P.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero P).mpr y.property
        rw [map_add, map_add, hz, hz, mkQ_sectionMap, mkQ_sectionMap,
          zero_add, zero_add] at hq
        exact hq
      have hab' : (a.1 : M) = (b.1 : M) := by
        change (a.1 : M) + sectionMap P a.2 = (b.1 : M) + sectionMap P b.2 at h
        rw [hab] at h
        exact add_right_cancel h
      exact Prod.ext (Subtype.ext hab') hab
    · intro x
      have hx : x - sectionMap P (P.mkQ x) ∈ P := by
        rw [← Submodule.Quotient.mk_eq_zero]
        change P.mkQ (x - sectionMap P (P.mkQ x)) = 0
        rw [map_sub, mkQ_sectionMap, sub_self]
      exact ⟨(⟨x - sectionMap P (P.mkQ x), hx⟩, P.mkQ x), sub_add_cancel _ _⟩)

@[simp] theorem equiv_apply (x : P × (M ⧸ P)) :
    equiv P x = (x.1 : M) + sectionMap P x.2 := rfl

/-- Extend a basis using a basis of the free quotient. -/
def basis (b : Module.Basis ι R P) (c : Module.Basis κ R (M ⧸ P)) :
    Module.Basis (ι ⊕ κ) R M := (b.prod c).map (equiv P)

@[simp] theorem basis_inl (b : Module.Basis ι R P) (c : Module.Basis κ R (M ⧸ P))
    (i : ι) : basis P b c (Sum.inl i) = (b i : M) := by
  simp [basis]

end Parafree.Linear.SplitBasis
