import Parafree.Homology.Coefficients.DimensionShift
import LieRings.UniversalEnveloping.Basic

/-! The left regular enveloping module and its split augmentation sequence.

The regular module is a type synonym, so the left multiplication action cannot be
confused with the adjoint action of the associative algebra. The augmentation and
its kernel are Lie-module maps; only the underlying linear sequence splits.
No PBW or acyclicity theorem is needed for this construction.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.Enveloping

universe u
variable (R L : Type u) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The enveloping algebra equipped below with its left regular Lie action. -/
def Regular := UniversalEnvelopingAlgebra R L

instance : AddCommGroup (Regular R L) := inferInstanceAs (AddCommGroup (LieRings.UEA R L))
instance : Module R (Regular R L) := inferInstanceAs (Module R (LieRings.UEA R L))

/-- Forget the regular-action type synonym. -/
def equiv : Regular R L ≃ₗ[R] LieRings.UEA R L := LinearEquiv.refl R _

instance : LieRingModule L (Regular R L) where
  bracket x a := (equiv R L).symm (UniversalEnvelopingAlgebra.ι R x * equiv R L a)
  add_lie x y a := by
    apply (equiv R L).injective
    change UniversalEnvelopingAlgebra.ι R (x + y) * equiv R L a =
      UniversalEnvelopingAlgebra.ι R x * equiv R L a +
        UniversalEnvelopingAlgebra.ι R y * equiv R L a
    rw [map_add, add_mul]
  lie_add x a b := by
    apply (equiv R L).injective
    change UniversalEnvelopingAlgebra.ι R x * (equiv R L a + equiv R L b) = _
    exact mul_add _ _ _
  leibniz_lie x y a := by
    apply (equiv R L).injective
    change UniversalEnvelopingAlgebra.ι R x * (UniversalEnvelopingAlgebra.ι R y * equiv R L a) =
      UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ * equiv R L a +
        UniversalEnvelopingAlgebra.ι R y * (UniversalEnvelopingAlgebra.ι R x * equiv R L a)
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, sub_mul, mul_assoc, mul_assoc]
    abel

instance : LieModule R L (Regular R L) where
  smul_lie r x a := by
    apply (equiv R L).injective
    change UniversalEnvelopingAlgebra.ι R (r • x) * equiv R L a =
      r • (UniversalEnvelopingAlgebra.ι R x * equiv R L a)
    rw [map_smul, smul_mul_assoc]
  lie_smul r x a := by
    apply (equiv R L).injective
    change UniversalEnvelopingAlgebra.ι R x * (r • equiv R L a) =
      r • (UniversalEnvelopingAlgebra.ι R x * equiv R L a)
    rw [mul_smul_comm]

@[simp] theorem equiv_lie (x : L) (a : Regular R L) :
    equiv R L ⁅x, a⁆ = UniversalEnvelopingAlgebra.ι R x * equiv R L a := rfl

/-- Right multiplication commutes with the left Lie action. This is the module side
on which the coefficient CE differential is linear. -/
def rightMultiplication (a : LieRings.UEA R L) : Regular R L →ₗ⁅R,L⁆ Regular R L :=
  { (equiv R L).symm.toLinearMap.comp
      ((LinearMap.mulRight R a).comp (equiv R L).toLinearMap) with
    map_lie' := by
      intro x b
      apply (equiv R L).injective
      change (UniversalEnvelopingAlgebra.ι R x * equiv R L b) * a =
        UniversalEnvelopingAlgebra.ι R x * (equiv R L b * a)
      exact mul_assoc _ _ _ }

theorem differential_rightMultiplication (a : LieRings.UEA R L) (n : ℕ)
    (c : Parafree.Linear.ExteriorTensor.Chain R L (Regular R L) (n + 1)) :
    chainMap (rightMultiplication R L a) n (differential R L (Regular R L) n c) =
      differential R L (Regular R L) n (chainMap (rightMultiplication R L a) (n + 1) c) :=
  chainMap_differential_apply (rightMultiplication R L a) n c

/-- The usual augmentation, as a map to the trivial Lie module. -/
def augmentation : Regular R L →ₗ⁅R,L⁆ Trivial R L :=
  { (TrivialLieModule.equiv R L R).symm.toLinearMap.comp
      ((LieRings.UEA.augmentation R L).toLinearMap.comp (equiv R L).toLinearMap) with
    map_lie' := by
      intro x a
      apply (TrivialLieModule.equiv R L R).injective
      change LieRings.UEA.augmentation R L
        (UniversalEnvelopingAlgebra.ι R x * equiv R L a) = 0
      rw [map_mul, LieRings.UEA.augmentation_ι, zero_mul] }

@[simp] theorem augmentation_apply (a : Regular R L) :
    TrivialLieModule.equiv R L R (augmentation R L a) =
      LieRings.UEA.augmentation R L (equiv R L a) := rfl

def ideal : LieSubmodule R L (Regular R L) := (augmentation R L).ker

/-- The scalar inclusion is a linear section, not asserted to be equivariant. -/
def scalarSection : Trivial R L →ₗ[R] Regular R L :=
  (equiv R L).symm.toLinearMap.comp
    ((Algebra.linearMap R (LieRings.UEA R L)).comp (TrivialLieModule.equiv R L R).toLinearMap)

@[simp] theorem augmentation_scalarSection (r : Trivial R L) :
    augmentation R L (scalarSection R L r) = r := by
  apply (TrivialLieModule.equiv R L R).injective
  exact LieRings.UEA.augmentation_algebraMap R L _

theorem augmentation_surjective : Function.Surjective (augmentation R L) :=
  fun r => ⟨scalarSection R L r, augmentation_scalarSection R L r⟩

theorem inclusion_augmentation_exact : Function.Exact (ideal R L).incl (augmentation R L) := by
  intro a
  constructor
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact b.property

/-- Subtracting the scalar part retracts onto the augmentation ideal. -/
def retraction : Regular R L →ₗ[R] ideal R L :=
  (LinearMap.id - (scalarSection R L).comp (augmentation R L).toLinearMap).codRestrict
    (ideal R L).toSubmodule (fun a => by
      change augmentation R L (a - scalarSection R L (augmentation R L a)) = 0
      rw [map_sub, augmentation_scalarSection, sub_self])

theorem retraction_inclusion :
    (retraction R L).comp (ideal R L).incl.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change (a : Regular R L) - scalarSection R L (augmentation R L a) = a
  rw [show augmentation R L a = 0 from a.property, map_zero, sub_zero]

/-- The augmentation sequence is short exact on coefficient CE chains without a basis. -/
theorem sequence_shortExact :
    (Coefficients.sequence (ideal R L).incl (augmentation R L)
      (LieModuleHom.comp_ker_incl (f := augmentation R L))).ShortExact :=
  sequence_shortExact_of_retraction (ideal R L).incl (augmentation R L)
    (LieModuleHom.comp_ker_incl (f := augmentation R L)) (inclusion_augmentation_exact R L)
    (augmentation_surjective R L) (retraction R L) (retraction_inclusion R L)

end Parafree.Homology.Coefficients.Enveloping
