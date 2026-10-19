import Parafree.Homology.LowDegreeWedges

noncomputable section

namespace Parafree.Homology.ExteriorScalarChange

open LieRings.Homological.LieHomology
open Parafree.Linear.ExteriorBaseChange
open scoped TensorProduct Parafree.Linear.ExteriorBaseChange

variable {R : Type*} [CommRing R] {L : Type*} [LieRing L] [LieAlgebra R L]
section Along

variable (S : Type*) [CommRing S] [Algebra R S]
  {K : Type*} [LieRing K] [LieAlgebra R K] [LieAlgebra S K] [IsScalarTower R S K]
  (f : L →ₗ⁅R⁆ K)

def along (n : ℕ) :=
  letI : Module R (⋀[S]^n K) := Module.compHom (⋀[S]^n K) (algebraMap R S)
  letI : SMul R (⋀[S]^n K) := (Module.compHom (⋀[S]^n K) (algebraMap R S)).toSMul
  letI : Module S K := (inferInstance : LieAlgebra S K).toModule
  letI : Module R L := (inferInstance : LieAlgebra R L).toModule
  letI : IsScalarTower R S (⋀[S]^n K) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  (exteriorPower.alternatingMapLinearEquiv
    ((show K [⋀^Fin n]→ₗ[R] (⋀[S]^n K) from
      { (exteriorPower.ιMulti S n).toMultilinearMap.restrictScalars R with
        map_eq_zero_of_eq' := (exteriorPower.ιMulti S n).map_eq_zero_of_eq }).compLinearMap
          f.toLinearMap) : (⋀[R]^n L) →ₗ[R] (⋀[S]^n K))

@[simp] theorem along_wedge (n : ℕ) (v : Fin n → L) :
    along S f n (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti S n (f ∘ v) := by
  letI : Module R (⋀[S]^n K) := Module.compHom (⋀[S]^n K) (algebraMap R S)
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

@[simp] theorem along_one (x : L) : along S f 1 (exteriorPower.ιMulti R 1 ![x]) =
    exteriorPower.ιMulti S 1 ![f x] := by
  rw [along_wedge]
  congr 1
  funext i
  fin_cases i
  rfl

@[simp] theorem along_two (x y : L) : along S f 2 (exteriorPower.ιMulti R 2 ![x, y]) =
    exteriorPower.ιMulti S 2 ![f x, f y] := by
  rw [along_wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem along_three (x y z : L) : along S f 3 (exteriorPower.ιMulti R 3 ![x, y, z]) =
    exteriorPower.ιMulti S 3 ![f x, f y, f z] := by
  rw [along_wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem along_differential_two_wedge (x y z : L) :
    along S f 2 (differential R L 2 (exteriorPower.ιMulti R 3 ![x, y, z])) =
      differential S K 2 (along S f 3 (exteriorPower.ιMulti R 3 ![x, y, z])) := by
  letI : Module R (⋀[S]^2 K) := Module.compHom (⋀[S]^2 K) (algebraMap R S)
  rw [differential_two_wedge, along_three, differential_two_wedge]
  rw [(along S f 2).map_sub, (along S f 2).map_add, (along S f 2).map_neg]
  rw [along_two, along_two, along_two, f.map_lie, f.map_lie, f.map_lie]

theorem along_commute (n m : ℕ)
    (d : (⋀[R]^n L) →ₗ[R] (⋀[R]^m L))
    (e : (⋀[S]^n K) →ₗ[S] (⋀[S]^m K))
    (h : ∀ v, along S f m (d (exteriorPower.ιMulti R n v)) =
      e (along S f n (exteriorPower.ιMulti R n v))) (x : ⋀[R]^n L) :
    along S f m (d x) = e (along S f n x) := by
  letI : Module R (⋀[S]^n K) := Module.compHom (⋀[S]^n K) (algebraMap R S)
  letI : Module R (⋀[S]^m K) := Module.compHom (⋀[S]^m K) (algebraMap R S)
  letI : SMul R (⋀[S]^n K) := (Module.compHom (⋀[S]^n K) (algebraMap R S)).toSMul
  letI : SMul R (⋀[S]^m K) := (Module.compHom (⋀[S]^m K) (algebraMap R S)).toSMul
  letI : IsScalarTower R S (⋀[S]^n K) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower R S (⋀[S]^m K) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have heq : (along S f m).comp d = (e.restrictScalars R).comp (along S f n) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    exact h
  exact LinearMap.congr_fun heq x

theorem along_differential_two (x : ⋀[R]^3 L) :
    along S f 2 (differential R L 2 x) = differential S K 2 (along S f 3 x) := by
  apply along_commute S f 3 2 (differential R L 2) (differential S K 2) _ x
  intro v
  have hv : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  rw [hv]
  exact along_differential_two_wedge S f (v 0) (v 1) (v 2)

theorem along_differential_one_wedge (x y : L) :
    along S f 1 (differential R L 1 (exteriorPower.ιMulti R 2 ![x, y])) =
      differential S K 1 (along S f 2 (exteriorPower.ιMulti R 2 ![x, y])) := by
  letI : Module R (⋀[S]^1 K) := Module.compHom (⋀[S]^1 K) (algebraMap R S)
  rw [differential_one_wedge, along_two, differential_one_wedge,
    (along S f 1).map_neg, along_one, f.map_lie]

theorem along_differential_one (x : ⋀[R]^2 L) :
    along S f 1 (differential R L 1 x) = differential S K 1 (along S f 2 x) := by
  apply along_commute S f 2 1 (differential R L 1) (differential S K 1) _ x
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv]
  exact along_differential_one_wedge S f (v 0) (v 1)
end Along

end Parafree.Homology.ExteriorScalarChange
