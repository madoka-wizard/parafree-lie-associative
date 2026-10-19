import Parafree.TheoremC.WordKernel

/-! The irreducible words for the extended presentation, with a certified
prefix parser. Indices of the extra letters are shifted by two. -/
namespace Parafree.TheoremD.NormalWords
open Parafree.TheoremC

abbrev Letter := Fin 6 ⊕ ℕ
abbrev Y (i : Fin 6) : Letter := Sum.inl i
abbrev Z (n : ℕ) : Letter := Sum.inr n
abbrev Word := List Letter

/-- Parse an initial string of middle letters followed by the final letter. -/
def parse : Word → Option (ℕ × Word)
  | [] => none
  | Sum.inr _ :: _ => none
  | Sum.inl i :: w =>
      if i = 1 then (parse w).map (fun p => (p.1+1,p.2))
      else if i = 2 then some (0,w) else none

def Normal : Word → Prop
  | [] => True
  | i :: w => Normal w ∧ (i = Y 0 → parse w = none)

abbrev BasisWord := {w : Word // Normal w}

@[simp] theorem normal_nil : Normal [] := trivial

theorem normal_tail {i : Letter} {w : Word} (h : Normal (i :: w)) : Normal w := h.1

theorem normal_prepend {i : Letter} {w : Word} (hi : i ≠ Y 0) (hw : Normal w) :
    Normal (i :: w) := ⟨hw, fun h => False.elim (hi h)⟩

theorem normal_suffix {v w : Word} (h : Normal (v ++ w)) : Normal w := by
  induction v with
  | nil => exact h
  | cons i v ih => exact ih h.1

theorem normal_append {v w : Word} (hv : ∀ i ∈ v, i ≠ Y 0) (hw : Normal w) :
    Normal (v ++ w) := by
  induction v with
  | nil => exact hw
  | cons i v ih =>
    apply normal_prepend (hv i (by simp))
    exact ih (fun j hj => hv j (by simp [hj]))

@[simp] theorem parse_middle (w : Word) : parse (Y 1 :: w) = (parse w).map (fun p => (p.1+1,p.2)) := by
  simp [parse]
@[simp] theorem parse_final (w : Word) : parse (Y 2 :: w) = some (0,w) := by simp [parse]

@[simp] theorem parse_block (n : ℕ) (w : Word) :
    parse (List.replicate n (Y 1) ++ Y 2 :: w) = some (n,w) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

/-- Successful parsing certifies the exact consumed prefix and remaining suffix. -/
theorem parse_spec {w : Word} {n : ℕ} {t : Word} (h : parse w = some (n,t)) :
    w = List.replicate n (Y 1) ++ Y 2 :: t := by
  induction w generalizing n t with
  | nil => simp [parse] at h
  | cons i w ih =>
    cases i with
    | inr i => simp [parse] at h
    | inl i =>
      by_cases hi : i = 1
      · subst i
        cases hp : parse w with
        | none => simp [parse, hp] at h
        | some p =>
          obtain ⟨m,s⟩ := p
          have he : m+1=n ∧ s=t := by simpa [parse, hp] using h
          obtain ⟨rfl,rfl⟩ := he
          rw [ih hp]
          simp [List.replicate_succ]
      · by_cases hj : i = 2
        · subst i
          have he : n=0 ∧ t=w := by simpa [parse] using h.symm
          obtain ⟨rfl,rfl⟩ := he
          rfl
        · simp [parse, hi, hj] at h

theorem normal_parse_suffix {w : Word} (hw : Normal w) {n : ℕ} {t : Word}
    (h : parse w = some (n,t)) : Normal t := by
  have he := parse_spec h
  rw [he] at hw
  exact (normal_suffix hw).1

def replacement (n : ℕ) : Word := Y 3 :: (List.replicate n (Y 4) ++ [Y 5])

theorem normal_replacement (n : ℕ) {w : Word} (hw : Normal w) : Normal (replacement n ++ w) := by
  apply normal_append _ hw
  intro i hi
  simp only [replacement, List.mem_cons, List.mem_append, List.mem_replicate,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | ⟨_,rfl⟩ | rfl <;> decide

/-- Count the auxiliary relator letters. -/
def countZ (w : Word) : ℕ := w.countP (fun i => i.isRight)

@[simp] theorem countZ_append (v w : Word) : countZ (v ++ w) = countZ v + countZ w :=
  List.countP_append
@[simp] theorem countZ_Y (i : Fin 6) (w : Word) : countZ (Y i :: w) = countZ w := by simp [countZ]
@[simp] theorem countZ_Z (n : ℕ) (w : Word) : countZ (Z n :: w) = countZ w + 1 := by simp [countZ]
@[simp] theorem countZ_replacement (n : ℕ) : countZ (replacement n) = 0 := by
  simp [replacement, countZ]

theorem countZ_parse_suffix {w : Word} {n : ℕ} {t : Word} (h : parse w = some (n,t)) :
    countZ w = countZ t := by
  rw [parse_spec h, countZ_append]
  simp [countZ]

end Parafree.TheoremD.NormalWords
