import Parafree.TheoremD.NormalWords

/-! Faithful encoding of normal words, retaining the extra letters as markers. -/
namespace Parafree.TheoremD.NormalWords
open Parafree.TheoremC
open WordKernel

abbrev TargetLetter := Fin 4 ⊕ ℕ

def extendedCode : Letter → List TargetLetter
  | Sum.inl i => (code i).map Sum.inl
  | Sum.inr n => [Sum.inr n]
def encodeExtended (w : Word) : List TargetLetter := w.flatMap extendedCode
@[simp] theorem encodeExtended_nil : encodeExtended [] = [] := rfl
@[simp] theorem encodeExtended_cons (i : Letter) (w : Word) :
    encodeExtended (i :: w) = extendedCode i ++ encodeExtended w := List.flatMap_cons
@[simp] theorem encodeExtended_append (v w : Word) :
    encodeExtended (v ++ w) = encodeExtended v ++ encodeExtended w := List.flatMap_append

theorem encodeExtended_ne_nil (i : Letter) (w : Word) : encodeExtended (i :: w) ≠ [] := by
  cases i with
  | inl i => fin_cases i <;> simp [extendedCode, code]
  | inr n => simp [extendedCode]

private theorem extendedOffset {v w : Word}
    (h : encodeExtended v = Sum.inl 1 :: encodeExtended w) :
    ∃ (n : ℕ) (p q : Word),
      v = List.replicate n (Y 1) ++ Y 2 :: p ∧
      w = List.replicate n (Y 4) ++ Y 5 :: q ∧ encodeExtended p = encodeExtended q := by
  induction v generalizing w with
  | nil => simp at h
  | cons i v ih =>
    cases i with
    | inr i => simp [extendedCode] at h
    | inl i =>
      cases w with
      | nil => fin_cases i <;> simp [extendedCode, code] at h
      | cons j w =>
        cases j with
        | inr j => fin_cases i <;> simp [extendedCode, code] at h
        | inl j =>
          fin_cases i <;> fin_cases j <;> simp [extendedCode, code] at h
          · obtain ⟨n,p,q,hv,hw,hpq⟩ := ih h
            refine ⟨n+1,p,q,?_,?_,hpq⟩
            · simp [List.replicate_succ, hv]
            · simp [List.replicate_succ, hw]
          · exact ⟨0,v,w,rfl,rfl,h⟩

private theorem extendedOffset_impossible {v w : Word}
    (hv : Normal (Y 0 :: v)) (he : encodeExtended v = Sum.inl 1 :: encodeExtended w) : False := by
  obtain ⟨n,p,q,hp,hq,hpq⟩ := extendedOffset he
  have hh := hv.2 rfl
  rw [hp, parse_block] at hh
  cases hh

theorem encodeExtended_injective_on_normal {v w : Word}
    (hv : Normal v) (hw : Normal w) (he : encodeExtended v = encodeExtended w) : v = w := by
  induction v generalizing w with
  | nil =>
    cases w with
    | nil => rfl
    | cons j w => exact False.elim (encodeExtended_ne_nil j w he.symm)
  | cons i v ih =>
    cases w with
    | nil => exact False.elim (encodeExtended_ne_nil i v he)
    | cons j w =>
      have same (hij : i=j) (ht : encodeExtended v = encodeExtended w) : i :: v = j :: w := by
        subst j
        exact congrArg (i :: ·) (ih hv.1 hw.1 ht)
      cases i with
      | inr n =>
        cases j with
        | inr m =>
          have hh : n=m ∧ encodeExtended v = encodeExtended w := by simpa [extendedCode] using he
          exact same (congrArg Sum.inr hh.1) hh.2
        | inl j => fin_cases j <;> simp [extendedCode, code] at he
      | inl i =>
        cases j with
        | inr m => fin_cases i <;> simp [extendedCode, code] at he
        | inl j =>
          fin_cases i <;> fin_cases j <;> simp [extendedCode, code] at he
          all_goals first
            | exact same rfl he
            | exact False.elim (extendedOffset_impossible hv he)
            | exact False.elim (extendedOffset_impossible hw he.symm)

theorem encodeExtended_injective : Function.Injective (fun w : BasisWord => encodeExtended w.val) :=
  fun v w h => Subtype.ext (encodeExtended_injective_on_normal v.property w.property h)

end Parafree.TheoremD.NormalWords
