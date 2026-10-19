import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Scalar change for exterior powers of free modules, with its formula on wedges. -/

noncomputable section

namespace Parafree.Linear.ExteriorBaseChange

open Module
open scoped TensorProduct

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
variable {M : Type*} [AddCommGroup M] [Module R M] (n : ℕ)

scoped instance exteriorModule : Module R (⋀[S]^n (S ⊗[R] M)) :=
  Module.compHom _ (algebraMap R S)

scoped instance exteriorTower : IsScalarTower R S (⋀[S]^n (S ⊗[R] M)) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def wedge : M [⋀^Fin n]→ₗ[R] (⋀[S]^n (S ⊗[R] M)) :=
  (show (S ⊗[R] M) [⋀^Fin n]→ₗ[R] (⋀[S]^n (S ⊗[R] M)) from
    { (exteriorPower.ιMulti S n).toMultilinearMap.restrictScalars R with
      map_eq_zero_of_eq' := (exteriorPower.ιMulti S n).map_eq_zero_of_eq }).compLinearMap
        (TensorProduct.mk R S M 1)

def inclusion : (⋀[R]^n M) →ₗ[R] (⋀[S]^n (S ⊗[R] M)) :=
  exteriorPower.alternatingMapLinearEquiv (wedge S n)

@[simp] theorem inclusion_wedge (v : Fin n → M) :
    inclusion S n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] v i) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The canonical scalar-extension map, defined without choosing a basis. -/
def map : S ⊗[R] (⋀[R]^n M) →ₗ[S] (⋀[S]^n (S ⊗[R] M)) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : S →ₗ[S] S).smulRight (inclusion S n))

@[simp] theorem map_tmul (s : S) (x : ⋀[R]^n M) :
    map S n (s ⊗ₜ[R] x) = s • inclusion S n x := rfl

variable {ι : Type*} [LinearOrder ι] (b : Basis ι R M)

/-- Comparison of the exterior bases before and after extending scalars. -/
def equivalence : (S ⊗[R] (⋀[R]^n M)) ≃ₗ[S] (⋀[S]^n (S ⊗[R] M)) :=
  ((b.exteriorPower n).baseChange S).equiv ((b.baseChange S).exteriorPower n) (Equiv.refl _)

theorem equivalence_toLinearMap : (equivalence S n b).toLinearMap = map S n := by
  apply ((b.exteriorPower n).baseChange S).ext
  intro i
  change ((b.exteriorPower n).baseChange S).equiv
    ((b.baseChange S).exteriorPower n) (Equiv.refl _) (((b.exteriorPower n).baseChange S) i) = _
  rw [Basis.equiv_apply]
  simp only [Equiv.refl_apply, Basis.baseChange_apply, map_tmul, one_smul,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, inclusion_wedge]
  congr 1
  funext j
  exact Basis.baseChange_apply S b _

@[simp] theorem equivalence_tmul_wedge (s : S) (v : Fin n → M) :
    equivalence S n b (s ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      s • exteriorPower.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] v i) := by
  change (equivalence S n b).toLinearMap _ = _
  rw [equivalence_toLinearMap, map_tmul, inclusion_wedge]

variable [Module.Free R M]

/-- Exterior scalar change with an automatically selected basis. -/
def freeEquiv : (S ⊗[R] (⋀[R]^n M)) ≃ₗ[S] (⋀[S]^n (S ⊗[R] M)) :=
  letI : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  equivalence S n (Module.Free.chooseBasis R M)

theorem freeEquiv_toLinearMap :
    (freeEquiv (R := R) (M := M) S n).toLinearMap = map S n := by
  letI : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  exact equivalence_toLinearMap S n (Module.Free.chooseBasis R M)

@[simp] theorem freeEquiv_one_tmul (x : ⋀[R]^n M) :
    freeEquiv S n ((1 : S) ⊗ₜ[R] x) = inclusion S n x := by
  change (freeEquiv S n).toLinearMap _ = _
  rw [freeEquiv_toLinearMap, map_tmul, one_smul]

end Parafree.Linear.ExteriorBaseChange
