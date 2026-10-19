import Parafree.Lie.ScalarExtension
import Parafree.Lie.IntegralFreeModule

/-! Free Lie algebras commute with extension of integral scalars.
The equivalence is constructed from the two universal properties, and retains
formulas on generators for comparison of presented relation ideals. -/

noncomputable section
namespace Parafree.Lie.FreeScalarExtension

open scoped TensorProduct

variable (S : Type*) [CommRing S]
variable {L : Type*} [LieRing L]

def unit : L →ₗ⁅ℤ⁆ S ⊗[ℤ] L where
  __ := TensorProduct.mk ℤ S L 1
  map_lie' {x y} := by
    change (1 : S) ⊗ₜ[ℤ] ⁅x, y⁆ = ⁅(1 : S) ⊗ₜ[ℤ] x, (1 : S) ⊗ₜ[ℤ] y⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]

/-- Scalar extension along an injective coefficient map preserves the integral
inclusion whenever the source module is flat. -/
theorem unit_injective [CharZero S] [Module.Flat ℤ L] :
    Function.Injective (unit S (L := L)) := by
  have h := (Module.Flat.rTensor_preserves_injective_linearMap (M := L)
    (Algebra.linearMap ℤ S) (Int.cast_injective (α := S))).comp
    (TensorProduct.lid ℤ L).symm.injective
  convert h using 1
  ext x
  simp [unit]
  rfl

variable (X : Type*)

def generatorMap : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ FreeLieAlgebra S X :=
  FreeLieAlgebra.lift ℤ (FreeLieAlgebra.of S)

def toFree : S ⊗[ℤ] FreeLieAlgebra ℤ X →ₗ⁅S⁆ FreeLieAlgebra S X :=
  ScalarExtension.lift S (generatorMap S X)

def fromFree : FreeLieAlgebra S X →ₗ⁅S⁆ S ⊗[ℤ] FreeLieAlgebra ℤ X :=
  FreeLieAlgebra.lift S (fun x => (1 : S) ⊗ₜ[ℤ] FreeLieAlgebra.of ℤ x)

@[simp] theorem toFree_tmul (s : S) (x : FreeLieAlgebra ℤ X) :
    toFree S X (s ⊗ₜ[ℤ] x) = s • generatorMap S X x := rfl

@[simp] theorem generatorMap_of (x : X) :
    generatorMap S X (FreeLieAlgebra.of ℤ x) = FreeLieAlgebra.of S x :=
  FreeLieAlgebra.lift_of_apply _ _

@[simp] theorem fromFree_of (x : X) :
    fromFree S X (FreeLieAlgebra.of S x) = (1 : S) ⊗ₜ[ℤ] FreeLieAlgebra.of ℤ x :=
  FreeLieAlgebra.lift_of_apply _ _

theorem toFree_fromFree : (toFree S X).comp (fromFree S X) = LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro x
  simp only [LieHom.comp_apply, fromFree_of, toFree_tmul, generatorMap_of,
    one_smul, LieHom.id_apply]

theorem fromFree_generatorMap (x : FreeLieAlgebra ℤ X) :
    fromFree S X (generatorMap S X x) = (1 : S) ⊗ₜ[ℤ] x := by
  let f : FreeLieAlgebra S X →ₗ⁅ℤ⁆ S ⊗[ℤ] FreeLieAlgebra ℤ X :=
    { (fromFree S X).toLinearMap.restrictScalars ℤ with map_lie' := (fromFree S X).map_lie _ _ }
  have h : f.comp (generatorMap S X) = unit S := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change fromFree S X (generatorMap S X (FreeLieAlgebra.of ℤ i)) = _
    rw [generatorMap_of, fromFree_of]
    rfl
  exact LieHom.congr_fun h x

theorem fromFree_toFree (x : S ⊗[ℤ] FreeLieAlgebra ℤ X) :
    fromFree S X (toFree S X x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s x =>
    rw [toFree_tmul, map_smul, fromFree_generatorMap,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The canonical scalar-extension equivalence of free Lie algebras. -/
def equiv : (S ⊗[ℤ] FreeLieAlgebra ℤ X) ≃ₗ⁅S⁆ FreeLieAlgebra S X :=
  LieEquiv.ofBijective (toFree S X)
    ⟨Function.LeftInverse.injective (fromFree_toFree S X),
      Function.RightInverse.surjective (fun x => LieHom.congr_fun (toFree_fromFree S X) x)⟩

/-- The integral generators embed in characteristic zero. -/
theorem generatorMap_injective [CharZero S] [Countable X] :
    Function.Injective (generatorMap S X) := by
  letI := integral_freeLie_free X
  intro x y h
  apply unit_injective S
  exact (fromFree_generatorMap S X x).symm.trans
    ((congrArg (fromFree S X) h).trans (fromFree_generatorMap S X y))

end Parafree.Lie.FreeScalarExtension
