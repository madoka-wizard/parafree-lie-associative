import Parafree.TheoremD.LayerEmbedding

/-! Multiplication of the leading kernel-power layers. -/
noncomputable section
namespace Parafree.TheoremD.LayerEmbedding
open Parafree.TheoremC
open Parafree.Associative FreeAugmentation
open NormalWords NormalRepresentation NormalBasis NormalFiltration
variable (k : Type*) [CommRing k]

def codeValue (i : Letter) : Target k := word k TargetLetter (extendedCode i)
def encodeWord (w : Word) : Target k := word k TargetLetter (encodeExtended w)

@[simp] theorem encodeWord_nil : encodeWord k [] = 1 := word_nil k TargetLetter
@[simp] theorem encodeWord_cons (i : Letter) (w : Word) :
    encodeWord k (i :: w) = codeValue k i * encodeWord k w := by
  exact word_append k TargetLetter _ _
@[simp] theorem encodeWord_append (v w : Word) :
    encodeWord k (v ++ w) = encodeWord k v * encodeWord k w := by
  unfold encodeWord
  rw [encodeExtended_append, word_append]
@[simp] theorem encodeWord_replicate (i : Letter) (n : ℕ) :
    encodeWord k (List.replicate n i) = codeValue k i ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, pow_succ']

theorem codeValue_relations (n : ℕ) :
    codeValue k (Y 0) * codeValue k (Y 1)^n * codeValue k (Y 2) =
      codeValue k (Y 3) * codeValue k (Y 4)^n * codeValue k (Y 5) := by
  have h := pow_intertwine
    (FreeAlgebra.ι k (Sum.inl (1 : Fin 4) : TargetLetter) * FreeAlgebra.ι k (Sum.inl 2))
    (FreeAlgebra.ι k (Sum.inl (1 : Fin 4) : TargetLetter))
    (FreeAlgebra.ι k (Sum.inl 2) * FreeAlgebra.ι k (Sum.inl (1 : Fin 4) : TargetLetter))
    (mul_assoc _ _ _) n
  simpa [codeValue, extendedCode, WordKernel.code, word_cons, mul_assoc] using congrArg
    (fun x : Target k => FreeAlgebra.ι k (Sum.inl (0 : Fin 4) : TargetLetter) * x *
      FreeAlgebra.ι k (Sum.inl (3 : Fin 4) : TargetLetter)) h

theorem encodeWord_parsed {w : Word} {n : ℕ} {t : Word} (hp : parse w = some (n,t)) :
    codeValue k (Y 0) * encodeWord k w = encodeWord k (replacement n ++ t) := by
  rw [parse_spec hp]
  simp only [replacement, encodeWord_cons, encodeWord_append, encodeWord_replicate,
    encodeWord_nil, mul_one]
  simpa only [mul_assoc] using congrArg (· * encodeWord k t) (codeValue_relations k n)

theorem rawPart_zero_of_higher (h : ℕ) {v : Space k} (hv : v ∈ level k (h+1)) : rawPart k h v = 0 := by
  have hh : v ∈ level k h := antitone k (Nat.le_succ h) hv
  have he := (part_zero_iff_mem_succ k h hh).mpr hv
  change encodeLinear k (part k h v) = 0
  rw [he, map_zero]

theorem rawPart_prepend_Y (i : Fin 6) (hi : Y i ≠ Y 0) (h : ℕ) (w : BasisWord) :
    rawPart k h (prependOp k (Y i) hi (basis k w)) = codeValue k (Y i) * rawPart k h (basis k w) := by
  rw [prependOp_basis]
  simp only [rawPart_basis, prepend, countZ_Y]
  split
  · exact encodeWord_cons k (Y i) w.val
  · simp

theorem rawPart_zOp_basis (n h : ℕ) (w : BasisWord) :
    rawPart k (h+1) (zOp k n (basis k w)) = codeValue k (Z n) * rawPart k h (basis k w) := by
  rw [zOp, prependOp_basis]
  simp only [rawPart_basis, prepend, countZ_Z, Nat.add_right_cancel_iff]
  split
  · exact encodeWord_cons k (Z n) w.val
  · simp

theorem rawPart_leading_basis (h : ℕ) (w : BasisWord) (hw : h ≤ countZ w.val) :
    rawPart k h (leading k (basis k w)) = codeValue k (Y 0) * rawPart k h (basis k w) := by
  rw [leading_basis]
  unfold leadingBasis
  split
  · simp only [rawPart_basis, countZ_Y]
    split
    · exact encodeWord_cons k (Y 0) w.val
    · simp
  · rename_i n t hp
    have hc : countZ w.val = countZ t := countZ_parse_suffix hp
    have ht : h ≤ countZ t := hc ▸ hw
    have hextra : rawPart k h (extra k n ⟨t,normal_parse_suffix w.property hp⟩) = 0 := by
      apply rawPart_zero_of_higher
      unfold extra
      split
      · exact (level k (h+1)).zero_mem
      · apply basis_mem
        simpa [prepend] using Nat.add_le_add_right ht 1
    rw [map_add, hextra, add_zero]
    simp only [rawPart_basis, replaced, countZ_append, countZ_replacement, Nat.zero_add, hc]
    split
    · exact (encodeWord_parsed k hp).symm
    · simp

theorem rawPart_yOp_basis (i : Fin 6) (h : ℕ) (w : BasisWord) (hw : h ≤ countZ w.val) :
    rawPart k h (yOp k i (basis k w)) = codeValue k (Y i) * rawPart k h (basis k w) := by
  fin_cases i
  · exact rawPart_leading_basis k h w hw
  all_goals exact rawPart_prepend_Y k _ _ h w

theorem rawPart_yOp (i : Fin 6) (h : ℕ) {v : Space k} (hv : v ∈ level k h) :
    rawPart k h (yOp k i v) = codeValue k (Y i) * rawPart k h v := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨w,hw,rfl⟩ := hv; exact rawPart_yOp_basis k i h w hw
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb, mul_add]
  | smul c v _ hv => simp [hv]

theorem rawPart_zOp (n h : ℕ) (v : Space k) :
    rawPart k (h+1) (zOp k n v) = codeValue k (Z n) * rawPart k h v := by
  have he : (rawPart k (h+1)).comp (zOp k n) =
      (LinearMap.mulLeft k (codeValue k (Z n))).comp (rawPart k h) := by
    apply (Finsupp.basisSingleOne : Module.Basis BasisWord k (Space k)).ext
    intro w
    exact rawPart_zOp_basis k n h w
  exact LinearMap.congr_fun he v

theorem rawPart_word_action (w : Word) (h : ℕ) {v : Space k} (hv : v ∈ level k h) :
    rawPart k (h+countZ w) (NormalRepresentation.hom k (wordValue k w) v) =
      encodeWord k w * rawPart k h v := by
  induction w with
  | nil => simp [countZ]
  | cons i w ih =>
    rw [wordValue_cons, map_mul, Module.End.mul_apply]
    cases i with
    | inl i =>
      change rawPart k (h+countZ (Y i :: w))
        (NormalRepresentation.hom k (1+generator₀ k i) _) = _
      rw [hom_shifted, countZ_Y, rawPart_yOp k i _ (word_action_mem k w h hv), ih,
        encodeWord_cons, mul_assoc]
    | inr n =>
      change rawPart k (h+countZ (Z n :: w))
        (NormalRepresentation.hom k (toInitial k (relator k (n+2))) _) = _
      rw [hom_higher_relator, countZ_Z, ← Nat.add_assoc, rawPart_zOp, ih,
        encodeWord_cons, mul_assoc]

end Parafree.TheoremD.LayerEmbedding
