import Parafree.Upstream.CE
import Parafree.TheoremA.CrossProduct
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Low-degree CE calculation for the signed cross-product algebra

The boundary here is the actual boundary in LieRings, not a separately defined complex.
Surjectivity is proved over every commutative ring with an explicit preimage.
-/

namespace Parafree.TheoremA.CrossProduct

open LieRings.Homological.LieHomology

variable (R : Type*) [CommRing R]

instance : Module.Free R (CrossProduct R) :=
  inferInstanceAs (Module.Free R (Fin 3 → R))

instance : Module.Finite R (CrossProduct R) :=
  inferInstanceAs (Module.Finite R (Fin 3 → R))

@[simp] theorem boundary_u_v :
    degreeTwoBoundary R (CrossProduct R) (exteriorPower.ιMulti R 2 ![u R, v R]) =
      -z R := by simp

@[simp] theorem boundary_v_z :
    degreeTwoBoundary R (CrossProduct R) (exteriorPower.ιMulti R 2 ![v R, z R]) =
      -u R := by simp

@[simp] theorem boundary_z_u :
    degreeTwoBoundary R (CrossProduct R) (exteriorPower.ιMulti R 2 ![z R, u R]) =
      v R := by simp

theorem degreeTwoBoundary_surjective :
    Function.Surjective (degreeTwoBoundary R (CrossProduct R)) := by
  intro x
  refine ⟨(-x 0) • exteriorPower.ιMulti R 2 ![u R, v R] +
    (-x 1) • exteriorPower.ιMulti R 2 ![v R, z R] +
    x 2 • exteriorPower.ιMulti R 2 ![z R, u R], ?_⟩
  simpa using (coordinates R x).symm

section Field

variable (k : Type*) [Field k]

@[simp] theorem finrank_eq_three : Module.finrank k (CrossProduct k) = 3 := by
  change Module.finrank k (Fin 3 → k) = 3
  simp

theorem degreeTwoBoundary_injective :
    Function.Injective (degreeTwoBoundary k (CrossProduct k)) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    (degreeTwoBoundary_surjective k)
  rw [exteriorPower.finrank_eq, finrank_eq_three]
  norm_num

theorem differential_one_injective :
    Function.Injective (differential k (CrossProduct k) 1) := by
  intro x y h
  apply degreeTwoBoundary_injective k
  exact congrArg (exteriorPower.oneEquiv k (CrossProduct k)) h

/-- The differential from degree three is zero, by square-zero and injectivity below it. -/
theorem differential_two_eq_zero : differential k (CrossProduct k) 2 = 0 := by
  apply LinearMap.ext
  intro x
  apply differential_one_injective k
  have h := LinearMap.congr_fun (differential_comp_differential k (CrossProduct k) 1) x
  simpa using h

/-- The second homology of the library's CE complex is zero. -/
theorem homologyTwo_subsingleton :
    Subsingleton (Homology (R := k) (L := CrossProduct k) 2) := by
  have hexact : (complex k (CrossProduct k)).ExactAt 2 := by
    apply (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (complex k (CrossProduct k)).d 2 ((ComplexShape.down ℕ).next 2) x = 0 at hx
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1,
      complex_d] at hx
    have hz : differential k (CrossProduct k) 1 0 = 0 :=
      (differential k (CrossProduct k) 1).map_zero
    have hx0 : x = 0 := differential_one_injective k (hx.trans hz.symm)
    subst x
    exact ⟨0, ((complex k (CrossProduct k)).sc 2).f.hom.map_zero⟩
  exact ModuleCat.isZero_iff_subsingleton.mp hexact.isZero_homology

theorem differential_three_eq_zero : differential k (CrossProduct k) 3 = 0 := by
  haveI : Subsingleton (⋀[k]^4 (CrossProduct k)) := by
    apply (Module.finrank_zero_iff (R := k)).mp
    rw [exteriorPower.finrank_eq, finrank_eq_three]
    norm_num
  apply LinearMap.ext
  intro x
  rw [Subsingleton.elim x 0, map_zero]
  rfl

/-- With both adjacent differentials zero, third homology is the top exterior power. -/
noncomputable def homologyThreeExteriorEquiv :
    Homology (R := k) (L := CrossProduct k) 3 ≃ₗ[k] ⋀[k]^3 (CrossProduct k) := by
  let S := (complex k (CrossProduct k)).sc 3
  have hf : S.f = 0 := by
    change (complex k (CrossProduct k)).d ((ComplexShape.down ℕ).prev 3) 3 = 0
    rw [show (ComplexShape.down ℕ).prev 3 = 4 from ChainComplex.prev ℕ 3,
      complex_d, differential_three_eq_zero]
    rfl
  have hg : S.g = 0 := by
    change (complex k (CrossProduct k)).d 3 ((ComplexShape.down ℕ).next 3) = 0
    rw [show (ComplexShape.down ℕ).next 3 = 2 from ChainComplex.next_nat_succ 2,
      complex_d, differential_two_eq_zero]
    rfl
  exact (CategoryTheory.ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyIso.toLinearEquiv

/-- The third CE homology is one copy of the coefficient field. -/
noncomputable def homologyThreeEquiv :
    Homology (R := k) (L := CrossProduct k) 3 ≃ₗ[k] k :=
  (homologyThreeExteriorEquiv k).trans (LinearEquiv.ofFinrankEq _ _ (by
    rw [exteriorPower.finrank_eq, finrank_eq_three]
    simp))

end Field
end Parafree.TheoremA.CrossProduct
