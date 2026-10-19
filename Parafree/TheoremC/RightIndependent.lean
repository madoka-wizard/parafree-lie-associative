import Parafree.TheoremC.Embedding

/-! The suffixes X₁(X₂X₃)^n form a suffix code. Consequently the right
multipliers (1+a)(1+b)^n are jointly left-linearly independent in A. -/
noncomputable section
namespace Parafree.TheoremC.RightIndependent
open Parafree.Associative.FreeAugmentation

abbrev Word := List (Fin 4)
def suffix : ℕ → Word
  | 0 => [0]
  | n+1 => suffix n ++ [1,2]

theorem suffixCode {v w : Word} {n m : ℕ}
    (h : v ++ suffix n = w ++ suffix m) : n = m ∧ v = w := by
  induction n generalizing m v w with
  | zero =>
    cases m with
    | zero => exact ⟨rfl,List.append_cancel_right h⟩
    | succ m =>
      have he := congrArg List.reverse h
      simp [suffix, List.reverse_append, List.reverse_cons] at he
  | succ n ih =>
    cases m with
    | zero =>
      have he := congrArg List.reverse h
      simp [suffix, List.reverse_append, List.reverse_cons] at he
    | succ m =>
      have hh : v ++ suffix n = w ++ suffix m :=
        List.append_cancel_right (by simpa only [suffix, List.append_assoc] using h)
      obtain ⟨rfl,rfl⟩ := ih hh
      exact ⟨rfl,rfl⟩

variable (k : Type*) [CommRing k]
abbrev Target := FreeAlgebra k (Fin 4)

def concatenate : (ℕ →₀ Target k) →ₗ[Target k] Target k :=
  Finsupp.linearCombination (Target k) (fun n => word k (Fin 4) (suffix n))

theorem concatenate_injective : Function.Injective (concatenate k) := by
  let b := Finsupp.basis (fun _ : ℕ => FreeAlgebra.basisFreeMonoid k (Fin 4))
  apply (concatenate k).restrictScalars k |>.injective_of_linearIndependent b.span_eq
  have hi : Function.Injective (fun p : Σ _ : ℕ, FreeMonoid (Fin 4) =>
      FreeMonoid.ofList (p.2.toList ++ suffix p.1)) := by
    rintro ⟨n,v⟩ ⟨m,w⟩ h
    have hh := suffixCode (congrArg FreeMonoid.toList h)
    obtain ⟨rfl,he⟩ := hh
    have hv : v = w := FreeMonoid.toList.injective he
    subst w
    rfl
  convert (FreeAlgebra.basisFreeMonoid k (Fin 4)).linearIndependent.comp _ hi using 1
  funext p
  simp only [Function.comp_apply, b, Finsupp.coe_basis, concatenate,
    LinearMap.restrictScalars_apply, Finsupp.linearCombination_single, smul_eq_mul]
  change word k (Fin 4) p.2.toList * word k (Fin 4) (suffix p.1) =
    word k (Fin 4) (p.2.toList ++ suffix p.1)
  exact (word_append k (Fin 4) _ _).symm

theorem word_suffix (n : ℕ) : word k (Fin 4) (suffix n) =
    Embedding.codeWord k 0 * Embedding.codeWord k 1 ^ n := by
  induction n with
  | zero => simp [suffix, Embedding.codeWord, WordKernel.code, word_cons]
  | succ n ih =>
    rw [suffix, word_append, ih, pow_succ, mul_assoc]
    rfl

def coefficients : (ℕ →₀ A k) →ₗ[k] (ℕ →₀ Target k) :=
  Finsupp.mapRange.linearMap (Embedding.hom k).toLinearMap

theorem coefficients_injective : Function.Injective (coefficients k) := by
  intro v w h
  ext n
  exact Embedding.hom_injective k (DFunLike.congr_fun h n)

def multiply : (ℕ →₀ A k) →ₗ[A k] A k :=
  Finsupp.linearCombination (A k) (fun n => (1+generator k 0) * (1+generator k 1)^n)

theorem hom_multiply (v : ℕ →₀ A k) :
    Embedding.hom k (multiply k v) = concatenate k (coefficients k v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single n a =>
    simp [multiply, concatenate, coefficients, word_suffix, Embedding.hom_generator]

theorem multiply_injective : Function.Injective (multiply k) := by
  intro v w h
  apply coefficients_injective k
  apply concatenate_injective k
  rw [← hom_multiply, ← hom_multiply, h]

end Parafree.TheoremC.RightIndependent
