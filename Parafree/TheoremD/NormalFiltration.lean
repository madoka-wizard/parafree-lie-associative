import Parafree.TheoremD.NormalBasis
import Parafree.TheoremC.FirstLimit

/-! The multiplicative filtration by the number of auxiliary relator letters. -/
noncomputable section
namespace Parafree.TheoremD.NormalFiltration
open Parafree.TheoremC
open Parafree.Associative NormalWords NormalRepresentation NormalBasis
variable (k : Type*) [CommRing k]

def level (h : ℕ) : Submodule k (Space k) :=
  Submodule.span k {v | ∃ w : BasisWord, h ≤ countZ w.val ∧ basis k w = v}

theorem level_eq_supported (h : ℕ) :
    level k h = Finsupp.supported k k {w : BasisWord | h ≤ countZ w.val} := by
  rw [Finsupp.supported_eq_span_single]
  rfl

theorem mem_level_iff (h : ℕ) (v : Space k) :
    v ∈ level k h ↔ ∀ w : BasisWord, countZ w.val < h → v w = 0 := by
  rw [level_eq_supported, Finsupp.mem_supported']
  simp

theorem basis_mem (h : ℕ) (w : BasisWord) (hw : h ≤ countZ w.val) : basis k w ∈ level k h :=
  Submodule.subset_span ⟨w,hw,rfl⟩

theorem antitone : Antitone (level k) := by
  intro m n hmn
  apply Submodule.span_mono
  rintro v ⟨w,hw,rfl⟩
  exact ⟨w,hmn.trans hw,rfl⟩

theorem level_zero : level k 0 = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  induction v using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | single w c =>
    simpa [basis] using (level k 0).smul_mem c (basis_mem k 0 w (Nat.zero_le _))

theorem leading_basis_mem (h : ℕ) (w : BasisWord) (hw : h ≤ countZ w.val) :
    leading k (basis k w) ∈ level k h := by
  rw [leading_basis]
  unfold leadingBasis
  split
  · apply basis_mem
    exact hw
  · rename_i n t hp
    have ht : h ≤ countZ t := by rwa [countZ_parse_suffix hp] at hw
    apply (level k h).add_mem
    · apply basis_mem
      simpa [replaced] using ht
    · unfold extra
      split
      · exact Submodule.zero_mem _
      · apply basis_mem
        simpa [prepend] using (ht.trans (Nat.le_succ _))

theorem yOp_basis_mem (i : Fin 6) (h : ℕ) (w : BasisWord) (hw : h ≤ countZ w.val) :
    yOp k i (basis k w) ∈ level k h := by
  fin_cases i
  · exact leading_basis_mem k h w hw
  all_goals
    rw [show yOp k _ = prependOp k _ _ from rfl, prependOp_basis]
    exact basis_mem k h _ hw

theorem zOp_basis_mem (n h : ℕ) (w : BasisWord) (hw : h ≤ countZ w.val) :
    zOp k n (basis k w) ∈ level k (h+1) := by
  rw [zOp, prependOp_basis]
  apply basis_mem
  simpa [prepend] using Nat.add_le_add_right hw 1

theorem yOp_mem (i : Fin 6) (h : ℕ) {v : Space k} (hv : v ∈ level k h) :
    yOp k i v ∈ level k h := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨w,hw,rfl⟩ := hv; exact yOp_basis_mem k i h w hw
  | zero => simp
  | add a b _ _ ha hb => simpa using (level k h).add_mem ha hb
  | smul c v _ hv => simpa using (level k h).smul_mem c hv

theorem zOp_mem (n h : ℕ) {v : Space k} (hv : v ∈ level k h) :
    zOp k n v ∈ level k (h+1) := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨w,hw,rfl⟩ := hv; exact zOp_basis_mem k n h w hw
  | zero => simp
  | add a b _ _ ha hb => simpa using (level k (h+1)).add_mem ha hb
  | smul c v _ hv => simpa using (level k (h+1)).smul_mem c hv

/-- Multiplication by a word cannot decrease its number of extra letters. -/
theorem word_action_mem (w : Word) (h : ℕ) {v : Space k} (hv : v ∈ level k h) :
    NormalRepresentation.hom k (wordValue k w) v ∈ level k (h + countZ w) := by
  induction w with
  | nil => simpa [countZ] using hv
  | cons i w ih =>
    rw [wordValue_cons, map_mul, Module.End.mul_apply]
    cases i with
    | inl i =>
      change NormalRepresentation.hom k (1+generator₀ k i) _ ∈ _
      rw [hom_shifted, countZ_Y]
      exact yOp_mem k i _ ih
    | inr n =>
      change NormalRepresentation.hom k (toInitial k (relator k (n+2))) _ ∈ _
      rw [hom_higher_relator, countZ_Z, ← Nat.add_assoc]
      exact zOp_mem k n _ ih

@[simp] theorem represent_mul (a b : A₀ k) : represent k (a*b) =
    NormalRepresentation.hom k a (represent k b) := by
  simp [represent, Module.End.mul_apply]

theorem mul_mem_level {m n : ℕ} {a b : A₀ k}
    (ha : represent k a ∈ level k m) (hb : represent k b ∈ level k n) :
    represent k (a*b) ∈ level k (m+n) := by
  have hgen : ∀ v ∈ level k m, represent k (evaluate k v * b) ∈ level k (m+n) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w,hw,rfl⟩ := hv
      rw [evaluate_basis, represent_mul]
      exact antitone k (by omega) (word_action_mem k w.val n hb)
    | zero => simp
    | add x y _ _ hx hy => simpa [add_mul] using (level k (m+n)).add_mem hx hy
    | smul c x _ hx => simpa [smul_mul_assoc] using (level k (m+n)).smul_mem c hx
  have h := hgen (represent k a) ha
  have he : evaluate k (represent k a) = a := LinearMap.congr_fun (evaluate_represent k) a
  rwa [he] at h

/-- The number-of-extra-letters subspace is actually a two-sided ideal. -/
def ideal (h : ℕ) : Ideal (A₀ k) where
  carrier := {a | represent k a ∈ level k h}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simpa using (level k h).add_mem ha hb
  smul_mem' := by
    intro a b hb
    have ha : represent k a ∈ level k 0 := by rw [level_zero]; trivial
    change represent k (a*b) ∈ level k h
    simpa only [Nat.zero_add] using mul_mem_level k ha hb

instance (h : ℕ) : (ideal k h).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    have hb : represent k b ∈ level k 0 := by rw [level_zero]; trivial
    simpa only [Nat.add_zero] using mul_mem_level k ha hb

end Parafree.TheoremD.NormalFiltration
