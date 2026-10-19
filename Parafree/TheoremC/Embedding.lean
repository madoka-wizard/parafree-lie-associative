import Parafree.TheoremC.Presentation
import Parafree.TheoremC.WordKernel
import Parafree.Associative.FreeWords

/-! Faithfulness of the manuscript's six-word realization of the full quotient. -/
noncomputable section
namespace Parafree.TheoremC.Embedding
open Parafree.Associative Parafree.Associative.FreeAugmentation
open WordKernel
variable (k : Type*) [CommRing k]

abbrev Target := FreeAlgebra k (Fin 4)
def codeWord (i : Fin 6) : Target k := word k (Fin 4) (code i)

theorem codeWord_relations (n : ℕ) :
    codeWord k 0 * codeWord k 1 ^ n * codeWord k 2 =
      codeWord k 3 * codeWord k 4 ^ n * codeWord k 5 := by
  have h := pow_intertwine
    (FreeAlgebra.ι k (1 : Fin 4) * FreeAlgebra.ι k 2) (FreeAlgebra.ι k (1 : Fin 4))
    (FreeAlgebra.ι k 2 * FreeAlgebra.ι k (1 : Fin 4)) (mul_assoc _ _ _) n
  simpa [codeWord, code, word_cons, mul_assoc] using congrArg
    (fun x : Target k => FreeAlgebra.ι k (0 : Fin 4) * x * FreeAlgebra.ι k (3 : Fin 4)) h

def onFree : Free k →ₐ[k] Target k := FreeAlgebra.lift k (fun i => codeWord k i - 1)

@[simp] theorem onFree_letter (i : Fin 6) : onFree k (letter k i) = codeWord k i - 1 :=
  FreeAlgebra.lift_ι_apply _ _

theorem onFree_relator (n : ℕ) : onFree k (relator k n) = 0 := by
  simpa [relator, ← add_sub_assoc] using sub_eq_zero.mpr (codeWord_relations k n)

def hom : A k →ₐ[k] Target k := quotientLift _ (onFree k)
  (twoSidedSpan_le (by rintro _ ⟨n,rfl⟩; exact onFree_relator k n))

@[simp] theorem hom_generator (i : Fin 6) : hom k (generator k i) = codeWord k i - 1 :=
  onFree_letter k i

def shiftedSurjection : Free k →ₐ[k] A k := FreeAlgebra.lift k (fun i => 1 + generator k i)
@[simp] theorem shiftedSurjection_ι (i : Fin 6) :
    shiftedSurjection k (FreeAlgebra.ι k i) = 1 + generator k i := FreeAlgebra.lift_ι_apply _ _

theorem shiftedSurjection_surjective : Function.Surjective (shiftedSurjection k) := by
  have he : (shiftedSurjection k).comp (shift k (Fin 6) (fun _ => -1)) = toFull k := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [generator, letter]
  intro x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective k (fullIdeal k) x
  exact ⟨shift k (Fin 6) (fun _ => -1) a, AlgHom.congr_fun he a⟩

theorem shifted_relations (n : ℕ) :
    (1+generator k 0) * (1+generator k 1)^n * (1+generator k 2) =
      (1+generator k 3) * (1+generator k 4)^n * (1+generator k 5) := by
  apply sub_eq_zero.mp
  simpa [relator, generator] using full_relator k n

theorem shifted_word_eq_of_encode_eq {v w : List (Fin 6)} (h : encode v = encode w) :
    shiftedSurjection k (word k (Fin 6) v) = shiftedSurjection k (word k (Fin 6) w) := by
  simp only [map_word, shiftedSurjection_ι]
  exact evaluate_eq_of_encode_eq (fun i => 1+generator k i) (shifted_relations k) v w h

theorem hom_shifted_word (w : List (Fin 6)) :
    hom k (shiftedSurjection k (word k (Fin 6) w)) = word k (Fin 4) (encode w) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, map_mul, map_mul, shiftedSurjection_ι, map_add, map_one,
      hom_generator, ih, encode_cons, word_append]
    simp [codeWord]

private def restoreWord (w : List (Fin 4)) : A k := by
  classical
  exact if h : ∃ v, encode v = w then shiftedSurjection k (word k (Fin 6) h.choose) else 0

private theorem restoreWord_encode (w : List (Fin 6)) :
    restoreWord k (encode w) = shiftedSurjection k (word k (Fin 6) w) := by
  rw [restoreWord, dif_pos ⟨w,rfl⟩]
  exact shifted_word_eq_of_encode_eq k (Exists.choose_spec (show ∃ v, encode v = encode w from ⟨w,rfl⟩))

private def restore : Target k →ₗ[k] A k :=
  (FreeAlgebra.basisFreeMonoid k (Fin 4)).constr k (fun w => restoreWord k w.toList)

private theorem restore_word (w : List (Fin 4)) :
    restore k (word k (Fin 4) w) = restoreWord k w :=
  (FreeAlgebra.basisFreeMonoid k (Fin 4)).constr_basis k _ _

theorem hom_injective : Function.Injective (hom k) := by
  have he : ((restore k).comp (hom k).toLinearMap).comp (shiftedSurjection k).toLinearMap =
      (shiftedSurjection k).toLinearMap := by
    apply (FreeAlgebra.basisFreeMonoid k (Fin 6)).ext
    intro w
    change restore k (hom k (shiftedSurjection k (word k (Fin 6) w.toList))) = _
    rw [hom_shifted_word, restore_word, restoreWord_encode]
    rfl
  have hl : Function.LeftInverse (restore k) (hom k) := by
    intro x
    obtain ⟨a,rfl⟩ := shiftedSurjection_surjective k x
    exact LinearMap.congr_fun he a
  exact hl.injective

end Parafree.TheoremC.Embedding
