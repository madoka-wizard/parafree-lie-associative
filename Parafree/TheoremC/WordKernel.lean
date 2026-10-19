import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! The six-word monoid map used in Sections C and D. -/
namespace Parafree.TheoremC.WordKernel

def code : Fin 6 → List (Fin 4) := ![[0], [1, 2], [1, 3], [0, 1], [2, 1], [3]]
def encode (w : List (Fin 6)) : List (Fin 4) := w.flatMap code
@[simp] theorem encode_nil : encode [] = [] := rfl
@[simp] theorem encode_cons (i : Fin 6) (w : List (Fin 6)) :
    encode (i :: w) = code i ++ encode w := List.flatMap_cons
@[simp] theorem encode_append (v w : List (Fin 6)) :
    encode (v ++ w) = encode v ++ encode w := List.flatMap_append

theorem encode_ne_nil {i : Fin 6} {w : List (Fin 6)} : encode (i :: w) ≠ [] := by
  fin_cases i <;> simp [code]

/-- An unmatched second alphabet letter forces a whole alternating block. -/
theorem offset {v w : List (Fin 6)} (h : encode v = 1 :: encode w) :
    ∃ (n : ℕ) (p q : List (Fin 6)),
      v = List.replicate n 1 ++ 2 :: p ∧
      w = List.replicate n 4 ++ 5 :: q ∧ encode p = encode q := by
  induction v generalizing w with
  | nil => simp at h
  | cons i v ih =>
    cases w with
    | nil => fin_cases i <;> simp [code] at h
    | cons j w =>
      fin_cases i <;> fin_cases j <;> simp [code] at h
      · obtain ⟨n,p,q,hv,hw,hpq⟩ := ih h
        refine ⟨n+1,p,q,?_,?_,hpq⟩
        · simp [List.replicate_succ, hv]
        · simp [List.replicate_succ, hw]
      · exact ⟨0,v,w,rfl,rfl,h⟩

variable {M : Type*} [Monoid M]
def evaluate (f : Fin 6 → M) (w : List (Fin 6)) : M := (w.map f).prod
@[simp] theorem evaluate_nil (f : Fin 6 → M) : evaluate f [] = 1 := rfl
@[simp] theorem evaluate_cons (f : Fin 6 → M) (i : Fin 6) (w : List (Fin 6)) :
    evaluate f (i :: w) = f i * evaluate f w := rfl
@[simp] theorem evaluate_append (f : Fin 6 → M) (v w : List (Fin 6)) :
    evaluate f (v ++ w) = evaluate f v * evaluate f w := by
  simp [evaluate, List.prod_append]
@[simp] theorem evaluate_replicate (f : Fin 6 → M) (n : ℕ) (i : Fin 6) :
    evaluate f (List.replicate n i) = f i ^ n := by simp [evaluate]

/-- Any monoid evaluation satisfying the displayed relations factors through `encode`. -/
theorem evaluate_eq_of_encode_eq (f : Fin 6 → M)
    (hf : ∀ n : ℕ, f 0 * f 1 ^ n * f 2 = f 3 * f 4 ^ n * f 5)
    (v w : List (Fin 6)) (h : encode v = encode w) : evaluate f v = evaluate f w := by
  induction v using (measure List.length).wf.induction generalizing w with
  | h v ih =>
    cases v with
    | nil =>
      cases w with
      | nil => rfl
      | cons j w => exact False.elim (encode_ne_nil h.symm)
    | cons i v =>
      cases w with
      | nil => exact False.elim (encode_ne_nil h)
      | cons j w =>
        have same (hij : i = j) (ht : encode v = encode w) :
            evaluate f (i :: v) = evaluate f (j :: w) := by
          subst j
          exact congrArg (f i * ·) (ih v (by change v.length < (i :: v).length; simp) w ht)
        have forward (hv : encode v = 1 :: encode w) :
            evaluate f (0 :: v) = evaluate f (3 :: w) := by
          obtain ⟨n,p,q,hp,hq,he⟩ := offset hv
          have hl : p.length < (i :: v).length := by
            rw [hp]
            simp only [List.length_cons, List.length_append, List.length_replicate]
            omega
          have hh := ih p hl q he
          simp only [hp,hq,evaluate_cons,evaluate_append,evaluate_replicate]
          rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, hf, hh]
        have backward (hv : encode w = 1 :: encode v) :
            evaluate f (3 :: v) = evaluate f (0 :: w) := by
          obtain ⟨n,p,q,hp,hq,he⟩ := offset hv
          have hl : q.length < (i :: v).length := by
            rw [hq]
            simp only [List.length_cons, List.length_append, List.length_replicate]
            omega
          have hh := ih q hl p he.symm
          simp only [hp,hq,evaluate_cons,evaluate_append,evaluate_replicate]
          rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, hf, hh]
        fin_cases i <;> fin_cases j <;> simp [code] at h
        all_goals first | exact same rfl h | exact forward h | exact backward h.symm

end Parafree.TheoremC.WordKernel
