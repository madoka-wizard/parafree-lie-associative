import Parafree.TheoremD.LayerAction
import Parafree.TheoremC.InitialHom

/-! Multiplication and augmentation compatibility of the layer detectors. -/
noncomputable section
namespace Parafree.TheoremD.LayerEmbedding
open Parafree.TheoremC
open Parafree.Associative FreeAugmentation
open NormalWords NormalRepresentation NormalBasis NormalFiltration
variable (k : Type*) [CommRing k]

theorem rawLayer_word (h : ℕ) (w : Word) (hw : Normal w) :
    rawLayer k h (wordValue k w) = if countZ w = h then encodeWord k w else 0 := by
  change rawPart k h (represent k (wordValue k w)) = _
  rw [represent_wordValue k w hw, rawPart_basis]
  rfl

theorem rawLayer_mul {m n : ℕ} {a b : A₀ k}
    (ha : a ∈ kernel k ^ m) (hb : b ∈ kernel k ^ n) :
    rawLayer k (m+n) (a*b) = rawLayer k m a * rawLayer k n b := by
  have hb' : represent k b ∈ level k n := (KernelBasis.mem_kernel_power_iff k n b).mp hb
  have hgen : ∀ v ∈ level k m,
      rawLayer k (m+n) (evaluate k v * b) = rawPart k m v * rawLayer k n b := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w,hw,rfl⟩ := hv
      rw [evaluate_basis]
      change rawPart k (m+n) (represent k (wordValue k w.val*b)) = _
      rw [represent_mul]
      by_cases hc : countZ w.val = m
      · rw [rawPart_basis, if_pos hc]
        simpa only [hc, Nat.add_comm] using rawPart_word_action k w.val n hb'
      · rw [rawPart_basis, if_neg hc, zero_mul]
        apply rawPart_zero_of_higher
        exact antitone k (by omega) (word_action_mem k w.val n hb')
    | zero => simp
    | add x y _ _ hx hy => simp [add_mul, hx, hy]
    | smul c x _ hx => simp [hx]
  have h := hgen (represent k a) ((KernelBasis.mem_kernel_power_iff k m a).mp ha)
  have he : evaluate k (represent k a) = a := LinearMap.congr_fun (evaluate_represent k) a
  simpa only [he] using h

theorem layer_mul {m n : ℕ} {a b : A₀ k}
    (ha : a ∈ kernel k ^ m) (hb : b ∈ kernel k ^ n) :
    layer k (m+n) (a*b) = layer k m a * layer k n b := by
  change translation k (rawLayer k (m+n) (a*b)) = _
  rw [rawLayer_mul k ha hb, map_mul]
  rfl

@[simp] theorem rawLayer_zero_one : rawLayer k 0 1 = 1 := by
  simpa [countZ] using rawLayer_word k 0 [] normal_nil

theorem mem_kernel_pow_zero (a : A₀ k) : a ∈ kernel k ^ 0 := by
  rw [Submodule.pow_zero, Ideal.one_eq_top]
  trivial

def zeroHom : A₀ k →ₐ[k] Target k := AlgHom.ofLinearMap (rawLayer k 0) (rawLayer_zero_one k)
  (fun a b => rawLayer_mul k (m := 0) (n := 0) (a := a) (b := b)
    (mem_kernel_pow_zero k a) (mem_kernel_pow_zero k b))

@[simp] theorem zeroHom_shifted (i : Fin 6) : zeroHom k (1+generator₀ k i) = codeValue k (Y i) := by
  have hw : Normal [Y i] := ⟨normal_nil, fun _ => rfl⟩
  simpa [wordValue, value, countZ] using rawLayer_word k 0 [Y i] hw

@[simp] theorem zeroHom_generator (i : Fin 6) : zeroHom k (generator₀ k i) = codeValue k (Y i) - 1 := by
  have h := congrArg (fun x : Target k => x-1) (zeroHom_shifted k i)
  simpa only [map_add, map_one, add_sub_cancel_left] using h

def translatedZeroHom : A₀ k →ₐ[k] Target k := (translation k).toAlgHom.comp (zeroHom k)

@[simp] theorem layer_zero_apply (a : A₀ k) : layer k 0 a = translatedZeroHom k a := rfl

@[simp] theorem augmentation_translatedCode (i : Fin 6) :
    FreeAlgebra.algebraMapInv (translation k (codeValue k (Y i))) = 1 := by
  fin_cases i <;> simp [translation, codeValue, extendedCode, WordKernel.code, word_cons,
    FreeAlgebra.algebraMapInv]

def augmentedZeroHom : AugmentedHom (augmentation₀ k)
    (FreeAlgebra.algebraMapInv : Target k →ₐ[k] k) where
  toAlgHom := translatedZeroHom k
  augmentation := by
    apply initialHom_ext
    intro i
    change FreeAlgebra.algebraMapInv (translation k (zeroHom k (generator₀ k i))) =
      augmentation₀ k (generator₀ k i)
    simp

theorem layer_zero_mem_augmentation {a : A₀ k} (ha : a ∈ initialAugmentationIdeal k) :
    layer k 0 a ∈ augmentationIdeal (FreeAlgebra.algebraMapInv : Target k →ₐ[k] k) := by
  change FreeAlgebra.algebraMapInv (translatedZeroHom k a) = 0
  exact ((augmentedZeroHom k).augmentation_apply a).trans ha

end Parafree.TheoremD.LayerEmbedding
