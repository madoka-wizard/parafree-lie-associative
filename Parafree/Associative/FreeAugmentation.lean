import Mathlib.LinearAlgebra.FreeAlgebra

/-!
# Last-letter decomposition of a free associative algebra

The augmentation ideal is a free left module, with one generator for each
letter. The inverse of concatenation removes the last letter of a nonempty
word. The resulting derivative has the augmented Leibniz rule, so its Lie
restriction can later be used to construct the equivariant relation map.
-/

noncomputable section

namespace Parafree.Associative.FreeAugmentation

open Module

universe u v
variable (R : Type u) (X : Type v) [CommRing R]

abbrev Algebra := FreeAlgebra R X

/-- The usual word basis, indexed by lists to expose the last-letter operation. -/
def word (w : List X) : Algebra R X := FreeAlgebra.basisFreeMonoid R X (FreeMonoid.ofList w)

theorem word_coordinates (w : List X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (word R X w) =
      Finsupp.single (FreeMonoid.ofList w) 1 := by
  simp [word, FreeAlgebra.basisFreeMonoid]
  exact FreeAlgebra.equivMonoidAlgebraFreeMonoid.apply_symm_apply _

@[simp] theorem word_nil : word R X [] = 1 := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  rw [word_coordinates, map_one]
  rfl

theorem word_concat (w : List X) (x : X) :
    word R X (w ++ [x]) = word R X w * FreeAlgebra.ι R x := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  rw [map_mul, word_coordinates, word_coordinates]
  have hι : FreeAlgebra.equivMonoidAlgebraFreeMonoid (FreeAlgebra.ι R x) =
      (Finsupp.single (FreeMonoid.of x) (1 : R) : MonoidAlgebra R (FreeMonoid X)) := by
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hι]
  rw [MonoidAlgebra.single_mul_single, one_mul]
  rfl

/-- Concatenate the distinguished last letter. This map is left-algebra-linear. -/
def concatenate : (X →₀ Algebra R X) →ₗ[Algebra R X] Algebra R X :=
  Finsupp.linearCombination (Algebra R X) (FreeAlgebra.ι R)

@[simp] theorem concatenate_single (x : X) (a : Algebra R X) :
    concatenate R X (Finsupp.single x a) = a * FreeAlgebra.ι R x :=
  Finsupp.linearCombination_single _ _ _

private def removeLast (w : List X) : X →₀ Algebra R X :=
  if h : w = [] then 0 else Finsupp.single (w.getLast h) (word R X w.dropLast)

/-- The linear last-letter derivative, with zero value on constants. -/
def derivative : Algebra R X →ₗ[R] (X →₀ Algebra R X) :=
  (FreeAlgebra.basisFreeMonoid R X).constr R
    (fun w => removeLast R X (FreeMonoid.toList w))

theorem derivative_word (w : List X) : derivative R X (word R X w) = removeLast R X w :=
  (FreeAlgebra.basisFreeMonoid R X).constr_basis R _ _

@[simp] theorem derivative_one : derivative R X 1 = 0 := by
  rw [← word_nil R X, derivative_word]
  simp [removeLast]

theorem derivative_word_concat (w : List X) (x : X) :
    derivative R X (word R X (w ++ [x])) = Finsupp.single x (word R X w) := by
  rw [derivative_word]
  simp [removeLast]

theorem derivative_concatenate_single (x : X) (a : Algebra R X) :
    derivative R X (concatenate R X (Finsupp.single x a)) = Finsupp.single x a := by
  have h : (derivative R X).comp
      (((concatenate R X).restrictScalars R).comp (Finsupp.lsingle x)) = Finsupp.lsingle x := by
    apply (FreeAlgebra.basisFreeMonoid R X).ext
    intro w
    change derivative R X (concatenate R X (Finsupp.single x (word R X w.toList))) = _
    rw [concatenate_single, ← word_concat, derivative_word_concat]
    rfl
  exact LinearMap.congr_fun h a

theorem derivative_concatenate (f : X →₀ Algebra R X) :
    derivative R X (concatenate R X f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x a => exact derivative_concatenate_single R X x a

theorem concatenate_injective : Function.Injective (concatenate R X) :=
  Function.LeftInverse.injective (derivative_concatenate R X)

theorem augmentation_word (w : List X) :
    FreeAlgebra.algebraMapInv (word R X w) = if w = [] then 1 else 0 := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w x _ =>
    rw [word_concat, map_mul]
    simp [FreeAlgebra.algebraMapInv]

/-- Reattaching the last letter recovers precisely the augmentation-zero part. -/
theorem concatenate_derivative (a : Algebra R X) :
    concatenate R X (derivative R X a) =
      a - algebraMap R (Algebra R X) (FreeAlgebra.algebraMapInv a) := by
  have h : ((concatenate R X).restrictScalars R).comp (derivative R X) =
      LinearMap.id - (Algebra.linearMap R (Algebra R X)).comp
        (FreeAlgebra.algebraMapInv : Algebra R X →ₐ[R] R).toLinearMap := by
    apply (FreeAlgebra.basisFreeMonoid R X).ext
    intro w
    change concatenate R X (derivative R X (word R X w.toList)) =
      word R X w.toList - algebraMap R (Algebra R X)
        (FreeAlgebra.algebraMapInv (word R X w.toList))
    induction w.toList using List.reverseRecOn with
    | nil => simp
    | append_singleton l x _ =>
      rw [derivative_word_concat, concatenate_single, augmentation_word]
      simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, if_false,
        map_zero, sub_zero, word_concat]
  exact LinearMap.congr_fun h a

theorem augmentation_concatenate (f : X →₀ Algebra R X) :
    FreeAlgebra.algebraMapInv (concatenate R X f) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single x a => simp [concatenate_single, FreeAlgebra.algebraMapInv]

/-- Exactness of the explicit free associative augmentation sequence. -/
theorem exact : Function.Exact (concatenate R X)
    (FreeAlgebra.algebraMapInv : Algebra R X →ₐ[R] R) := by
  intro a
  constructor
  · intro ha
    refine ⟨derivative R X a, ?_⟩
    rw [concatenate_derivative, ha, map_zero, sub_zero]
  · rintro ⟨f, rfl⟩
    exact augmentation_concatenate R X f

/-- The augmentation kernel, retaining its left-algebra module structure. -/
def ideal : Submodule (Algebra R X) (Algebra R X) where
  carrier := {a | FreeAlgebra.algebraMapInv a = 0}
  zero_mem' := map_zero _
  add_mem' := by
    intro a b ha hb
    change FreeAlgebra.algebraMapInv (a + b) = 0
    rw [map_add, ha, hb, add_zero]
  smul_mem' := by
    intro a b hb
    change FreeAlgebra.algebraMapInv (a * b) = 0
    rw [map_mul, hb, mul_zero]

/-- An explicit free left-module basis of the augmentation ideal. -/
def idealEquiv : (X →₀ Algebra R X) ≃ₗ[Algebra R X] ideal R X :=
  { (concatenate R X).codRestrict (ideal R X) (augmentation_concatenate R X) with
    invFun := fun a => derivative R X a
    left_inv := derivative_concatenate R X
    right_inv := by
      intro a
      apply Subtype.ext
      exact (concatenate_derivative R X a).trans (by
        rw [show FreeAlgebra.algebraMapInv (a : Algebra R X) = 0 from a.property,
          map_zero, sub_zero]) }

/-- The augmented Leibniz rule. Scalars in the second summand act centrally. -/
theorem derivative_mul (a b : Algebra R X) :
    derivative R X (a * b) = a • derivative R X b +
      (FreeAlgebra.algebraMapInv b) • derivative R X a := by
  apply concatenate_injective R X
  simp only [map_add, map_smul, LinearMap.map_smul_of_tower, concatenate_derivative,
    map_mul, smul_eq_mul, Algebra.smul_def, mul_sub]
  rw [Algebra.commutes (FreeAlgebra.algebraMapInv b) a,
    (Algebra.commutes (FreeAlgebra.algebraMapInv b)
      (algebraMap R (Algebra R X) (FreeAlgebra.algebraMapInv a)))]
  abel

/-- The formula used for equivariance of the relation map before coinvariants. -/
theorem derivative_commutator (a b : Algebra R X)
    (ha : FreeAlgebra.algebraMapInv a = 0) (hb : FreeAlgebra.algebraMapInv b = 0) :
    derivative R X (a * b - b * a) = a • derivative R X b - b • derivative R X a := by
  rw [map_sub, derivative_mul, derivative_mul, ha, hb, zero_smul, zero_smul,
    add_zero, add_zero]

end Parafree.Associative.FreeAugmentation
