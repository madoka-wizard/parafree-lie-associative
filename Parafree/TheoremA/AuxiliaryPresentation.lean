import Parafree.TheoremA.CrossProduct
import Parafree.Lie.Quotient
import Mathlib.Algebra.Lie.Free

/-! The three-relator auxiliary presentation is the signed rank-three algebra. -/

namespace Parafree.TheoremA

open Parafree.Lie

noncomputable section

namespace CrossProduct

variable (R : Type*) [CommRing R]
variable {M : Type*} [LieRing M] [LieAlgebra R M]

/-- The universal map determined by a triple satisfying the structure equations. -/
def lift (z' u' v' : M) (huv : ⁅u', v'⁆ = z') (hvz : ⁅v', z'⁆ = u')
    (hzu : ⁅z', u'⁆ = -v') : CrossProduct R →ₗ⁅R⁆ M where
  toFun x := x 0 • z' + x 1 • u' + x 2 • v'
  map_add' x y := by simp only [add_apply, add_smul]; abel
  map_smul' r x := by simp only [smul_apply, smul_add, mul_smul, RingHom.id_apply]
  map_lie' {x y} := by
    have hvu : ⁅v', u'⁆ = -z' := by rw [← lie_skew, huv]
    have hzv : ⁅z', v'⁆ = -u' := by rw [← lie_skew, hvz]
    have huz : ⁅u', z'⁆ = v' := by rw [← lie_skew, hzu, neg_neg]
    simp [bracket_apply, add_lie, lie_add, smul_lie, lie_smul,
      huv, hvz, hzu, hvu, hzv, huz]
    module

@[simp] theorem lift_z (z' u' v' : M) (huv : ⁅u', v'⁆ = z') (hvz : ⁅v', z'⁆ = u')
    (hzu : ⁅z', u'⁆ = -v') : lift R z' u' v' huv hvz hzu (z R) = z' := by
  simp [lift, z]

@[simp] theorem lift_u (z' u' v' : M) (huv : ⁅u', v'⁆ = z') (hvz : ⁅v', z'⁆ = u')
    (hzu : ⁅z', u'⁆ = -v') : lift R z' u' v' huv hvz hzu (u R) = u' := by
  simp [lift, u]

@[simp] theorem lift_v (z' u' v' : M) (huv : ⁅u', v'⁆ = z') (hvz : ⁅v', z'⁆ = u')
    (hzu : ⁅z', u'⁆ = -v') : lift R z' u' v' huv hvz hzu (v R) = v' := by
  simp [lift, v]

theorem hom_ext {f g : CrossProduct R →ₗ⁅R⁆ M}
    (hz : f (z R) = g (z R)) (hu : f (u R) = g (u R))
    (hv : f (v R) = g (v R)) : f = g := by
  apply LieHom.ext
  intro x
  rw [coordinates R x]
  simp only [map_add, map_smul, hz, hu, hv]

end CrossProduct

namespace Auxiliary

variable (R : Type*) [CommRing R]

abbrev Free := FreeLieAlgebra R (Fin 3)

def generator (i : Fin 3) : Free R := FreeLieAlgebra.of R i

def relator : Fin 3 → Free R :=
  ![generator R 0 - ⁅generator R 1, generator R 2⁆,
    generator R 1 - ⁅generator R 2, generator R 0⁆,
    generator R 2 + ⁅generator R 0, generator R 1⁆]

def relationIdeal : LieIdeal R (Free R) :=
  LieSubmodule.lieSpan R (Free R) (Set.range (relator R))

abbrev Presented := Free R ⧸ relationIdeal R

def gen (i : Fin 3) : Presented R := quotientMk (relationIdeal R) (generator R i)

theorem relator_zero (i : Fin 3) : quotientMk (relationIdeal R) (relator R i) = 0 :=
  (quotientMk_eq_zero _ _).mpr (LieSubmodule.subset_lieSpan (Set.mem_range_self i))

theorem lie_gen_one_two : ⁅gen R 1, gen R 2⁆ = gen R 0 := by
  have h := relator_zero R 0
  change quotientMk (relationIdeal R) (generator R 0 - ⁅generator R 1, generator R 2⁆) = 0 at h
  rw [map_sub, LieHom.map_lie] at h
  exact (sub_eq_zero.mp h).symm

theorem lie_gen_two_zero : ⁅gen R 2, gen R 0⁆ = gen R 1 := by
  have h := relator_zero R 1
  change quotientMk (relationIdeal R) (generator R 1 - ⁅generator R 2, generator R 0⁆) = 0 at h
  rw [map_sub, LieHom.map_lie] at h
  exact (sub_eq_zero.mp h).symm

theorem lie_gen_zero_one : ⁅gen R 0, gen R 1⁆ = -gen R 2 := by
  have h := relator_zero R 2
  change quotientMk (relationIdeal R) (generator R 2 + ⁅generator R 0, generator R 1⁆) = 0 at h
  rw [map_add, LieHom.map_lie] at h
  exact (eq_neg_of_add_eq_zero_right h)

def freeEvaluation : Free R →ₗ⁅R⁆ CrossProduct R :=
  FreeLieAlgebra.lift R ![CrossProduct.z R, CrossProduct.u R, CrossProduct.v R]

@[simp] theorem freeEvaluation_generator (i : Fin 3) :
    freeEvaluation R (generator R i) =
      ![CrossProduct.z R, CrossProduct.u R, CrossProduct.v R] i :=
  FreeLieAlgebra.lift_of_apply _ i

def toCrossProduct : Presented R →ₗ⁅R⁆ CrossProduct R :=
  quotientLift (relationIdeal R) (freeEvaluation R) (by
    apply LieSubmodule.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    change freeEvaluation R (relator R i) = 0
    fin_cases i <;> simp [relator, LieHom.map_lie])

@[simp] theorem toCrossProduct_gen (i : Fin 3) :
    toCrossProduct R (gen R i) =
      ![CrossProduct.z R, CrossProduct.u R, CrossProduct.v R] i :=
  freeEvaluation_generator R i

def fromCrossProduct : CrossProduct R →ₗ⁅R⁆ Presented R :=
  CrossProduct.lift R (gen R 0) (gen R 1) (gen R 2)
    (lie_gen_one_two R) (lie_gen_two_zero R) (lie_gen_zero_one R)

theorem to_from : (toCrossProduct R).comp (fromCrossProduct R) = LieHom.id := by
  apply CrossProduct.hom_ext
  all_goals simp [LieHom.comp_apply, fromCrossProduct]

theorem from_to : (fromCrossProduct R).comp (toCrossProduct R) = LieHom.id := by
  apply quotient_hom_ext
  apply FreeLieAlgebra.hom_ext
  intro i
  change fromCrossProduct R (toCrossProduct R (gen R i)) = gen R i
  rw [toCrossProduct_gen]
  fin_cases i <;> simp [fromCrossProduct]

/-- The presentation comparison in Lemma S, valid over every commutative ring. -/
def equivCrossProduct : Presented R ≃ₗ⁅R⁆ CrossProduct R :=
  LieEquiv.ofBijective (toCrossProduct R)
    ⟨Function.LeftInverse.injective (show Function.LeftInverse (fromCrossProduct R)
        (toCrossProduct R) from fun x => DFunLike.congr_fun (from_to R) x),
      Function.RightInverse.surjective (show Function.RightInverse (fromCrossProduct R)
        (toCrossProduct R) from fun x => DFunLike.congr_fun (to_from R) x)⟩

end Auxiliary
end
end Parafree.TheoremA
