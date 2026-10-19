import Parafree.Associative.Augmentation
import Parafree.Associative.UnitRelations
import Mathlib.Algebra.FreeAlgebra

/-! The exact two-relator algebra and its infinitely presented quotient.
The six free generators have augmentation zero, in the manuscript's order. -/
noncomputable section
namespace Parafree.TheoremC
open Parafree.Associative
variable (k : Type*) [CommRing k]

abbrev Free := FreeAlgebra k (Fin 6)
def letter (i : Fin 6) : Free k := FreeAlgebra.ι k i

def relator (n : ℕ) : Free k :=
  (1 + letter k 0) * (1 + letter k 1) ^ n * (1 + letter k 2) -
    (1 + letter k 3) * (1 + letter k 4) ^ n * (1 + letter k 5)

def initialIdeal : Ideal (Free k) := twoSidedSpan (Set.range (fun i : Fin 2 => relator k i))
def fullIdeal : Ideal (Free k) := twoSidedSpan (Set.range (relator k))
instance : (initialIdeal k).IsTwoSided := inferInstanceAs (twoSidedSpan _).IsTwoSided
instance : (fullIdeal k).IsTwoSided := inferInstanceAs (twoSidedSpan _).IsTwoSided

abbrev A₀ := Free k ⧸ initialIdeal k
abbrev A := Free k ⧸ fullIdeal k

def toInitial : Free k →ₐ[k] A₀ k := Ideal.Quotient.mkₐ k _
def toFull : Free k →ₐ[k] A k := Ideal.Quotient.mkₐ k _
def generator₀ (i : Fin 6) : A₀ k := toInitial k (letter k i)
def generator (i : Fin 6) : A k := toFull k (letter k i)

def freeAugmentation : Free k →ₐ[k] k := FreeAlgebra.lift k (fun _ => 0)

@[simp] theorem freeAugmentation_letter (i : Fin 6) : freeAugmentation k (letter k i) = 0 :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem freeAugmentation_relator (n : ℕ) : freeAugmentation k (relator k n) = 0 := by
  simp [relator]

theorem initialIdeal_le_full : initialIdeal k ≤ fullIdeal k :=
  twoSidedSpan_le (by rintro _ ⟨i,rfl⟩; exact subset_twoSidedSpan ⟨(i:ℕ),rfl⟩)

theorem fullIdeal_le_augmentation : fullIdeal k ≤ augmentationIdeal (freeAugmentation k) :=
  twoSidedSpan_le (by rintro _ ⟨n,rfl⟩; exact freeAugmentation_relator k n)

def augmentation₀ : A₀ k →ₐ[k] k := quotientLift _ (freeAugmentation k)
  ((initialIdeal_le_full k).trans (fullIdeal_le_augmentation k))
def augmentation : A k →ₐ[k] k := quotientLift _ (freeAugmentation k) (fullIdeal_le_augmentation k)

@[simp] theorem augmentation₀_toInitial (x : Free k) : augmentation₀ k (toInitial k x) = freeAugmentation k x := rfl
@[simp] theorem augmentation_toFull (x : Free k) : augmentation k (toFull k x) = freeAugmentation k x := rfl
@[simp] theorem augmentation₀_generator (i : Fin 6) : augmentation₀ k (generator₀ k i) = 0 := freeAugmentation_letter k i
@[simp] theorem augmentation_generator (i : Fin 6) : augmentation k (generator k i) = 0 := freeAugmentation_letter k i

def projection : A₀ k →ₐ[k] A k := Ideal.Quotient.factorₐ k (initialIdeal_le_full k)
@[simp] theorem projection_toInitial (x : Free k) : projection k (toInitial k x) = toFull k x := rfl

theorem projection_surjective : Function.Surjective (projection k) := by
  intro x
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mkₐ_surjective k (fullIdeal k) x
  exact ⟨toInitial k x,rfl⟩

def augmentedProjection : AugmentedHom (augmentation₀ k) (augmentation k) where
  toAlgHom := projection k
  augmentation := by apply Ideal.Quotient.algHom_ext k; rfl

def kernel : Ideal (A₀ k) := RingHom.ker (projection k)
instance : (kernel k).IsTwoSided := inferInstanceAs (RingHom.ker _).IsTwoSided

def fourToInitial : FreeAlgebra k (Fin 4) →ₐ[k] A₀ k :=
  FreeAlgebra.lift k (fun i => generator₀ k i.castSucc.castSucc)
def fourToFull : FreeAlgebra k (Fin 4) →ₐ[k] A k := (projection k).comp (fourToInitial k)

def fourAugmentation : FreeAlgebra k (Fin 4) →ₐ[k] k := FreeAlgebra.lift k (fun _ => 0)

def augmentedFourToInitial : AugmentedHom (fourAugmentation k) (augmentation₀ k) where
  toAlgHom := fourToInitial k
  augmentation := by
    apply FreeAlgebra.hom_ext
    funext i
    simpa only [Function.comp_apply, AlgHom.comp_apply, fourToInitial, fourAugmentation,
      FreeAlgebra.lift_ι_apply] using augmentation₀_generator k i.castSucc.castSucc

@[simp] theorem initial_relator (i : Fin 2) : toInitial k (relator k i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (subset_twoSidedSpan ⟨i,rfl⟩)
@[simp] theorem full_relator (n : ℕ) : toFull k (relator k n) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (subset_twoSidedSpan ⟨n,rfl⟩)

end Parafree.TheoremC
