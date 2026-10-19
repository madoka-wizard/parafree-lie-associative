import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! Finite families in a family of submodules, with an explicit ambient
finite-support representative. -/

noncomputable section
namespace Parafree.Linear

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [DecidableEq ι] (E : ι → Submodule R M)

/-- Forget the individual submodule conditions in a finite dependent family. -/
def submoduleFamilyValue : (Π₀ i, E i) →ₗ[R] (ι →₀ M) := by
  classical
  exact DFinsupp.lsum R (fun i => (Finsupp.lsingle i).comp (E i).subtype)

@[simp] theorem submoduleFamilyValue_single (i : ι) (x : E i) :
    submoduleFamilyValue E (DFinsupp.single i x) = Finsupp.single i (x : M) := by
  classical
  simp [submoduleFamilyValue]

@[simp] theorem submoduleFamilyValue_apply (x : Π₀ i, E i) (i : ι) :
    submoduleFamilyValue E x i = (x i : M) := by
  classical
  induction x using DFinsupp.induction with
  | h0 => simp only [map_zero, Finsupp.zero_apply, DFinsupp.zero_apply, ZeroMemClass.coe_zero]
  | @ha j a x _ _ ih =>
    rw [map_add, Finsupp.add_apply, submoduleFamilyValue_single]
    by_cases h : i = j
    · subst i; simpa only [DFinsupp.add_apply, DFinsupp.single_eq_same,
        AddMemClass.coe_add, Finsupp.single_eq_same] using congrArg ((a : M) + ·) ih
    · simpa only [DFinsupp.add_apply, DFinsupp.single_eq_of_ne h,
        AddMemClass.coe_add, ZeroMemClass.coe_zero, Finsupp.single_eq_of_ne h,
        zero_add] using ih

/-- The same map with its coordinatewise membership proofs retained. -/
def submoduleFamily : (Π₀ i, E i) →ₗ[R] Finsupp.submodule E :=
  (submoduleFamilyValue E).codRestrict _ (fun x i => by
    rw [submoduleFamilyValue_apply]
    exact (x i).property)

@[simp] theorem submoduleFamily_apply (x : Π₀ i, E i) (i : ι) :
    ((submoduleFamily E x : Finsupp.submodule E) : ι →₀ M) i = (x i : M) :=
  submoduleFamilyValue_apply E x i

end Parafree.Linear
