import LieRings.PBW.Collection

/-!
# The word filtration of a universal enveloping algebra

The filtration is defined intrinsically, without choosing a basis. Products add
filtration bounds, it is exhaustive, and permuting a word changes it only by a
term of strictly smaller word length. These are the collection estimates needed
to compare a PBW resolution with its polynomial leading complex.
-/

noncomputable section

namespace Parafree.Associative.EnvelopingFiltration

open LieRings LieRings.PBW

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

def level (n : ℕ) : Submodule R (UEA R L) :=
  Submodule.span R {a | ∃ xs : List L, xs.length ≤ n ∧ envelopingWord R L xs = a}

theorem word_mem (xs : List L) {n : ℕ} (hn : xs.length ≤ n) :
    envelopingWord R L xs ∈ level R L n :=
  Submodule.subset_span ⟨xs, hn, rfl⟩

theorem monotone : Monotone (level R L) := by
  intro m n hmn
  apply Submodule.span_mono
  rintro a ⟨xs, hx, rfl⟩
  exact ⟨xs, hx.trans hmn, rfl⟩

theorem one_mem (n : ℕ) : (1 : UEA R L) ∈ level R L n :=
  word_mem R L [] (Nat.zero_le n)

theorem iota_mem (x : L) : UniversalEnvelopingAlgebra.ι R x ∈ level R L 1 := by
  simpa using word_mem R L [x] (le_refl 1)

theorem mul_mem {m n : ℕ} {a b : UEA R L}
    (ha : a ∈ level R L m) (hb : b ∈ level R L n) : a * b ∈ level R L (m + n) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨xs, hxs, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨ys, hys, rfl⟩ := hb
      rw [← envelopingWord_append]
      exact word_mem R L _ (by simpa only [List.length_append] using Nat.add_le_add hxs hys)
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using (level R L (m + n)).add_mem hb hc
    | smul r b _ hb => simpa only [mul_smul_comm] using (level R L (m + n)).smul_mem r hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (level R L (m + n)).add_mem ha hc
  | smul r a _ ha => simpa only [smul_mul_assoc] using (level R L (m + n)).smul_mem r ha

theorem exhaustive (a : UEA R L) : ∃ n, a ∈ level R L n := by
  induction a using LieRings.UEA.induction with
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact (level R L 0).smul_mem r (one_mem R L 0)
  | ι x => exact ⟨1, iota_mem R L x⟩
  | mul a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, mul_mem R L hm hn⟩
  | add a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨max m n, (level R L _).add_mem
      (monotone R L (le_max_left m n) hm) (monotone R L (le_max_right m n) hn)⟩

/-- Adjacent swaps and their composites lower word length by at least one. -/
theorem perm_sub_mem {xs ys : List L} (h : xs.Perm ys) (n : ℕ)
    (hn : xs.length ≤ n + 1) :
    envelopingWord R L xs - envelopingWord R L ys ∈ level R L n := by
  induction h generalizing n with
  | nil => simp only [sub_self]; exact (level R L n).zero_mem
  | @cons x xs ys h ih =>
    cases n with
    | zero =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using hn)
      have hy : ys = [] := List.length_eq_zero_iff.mp (by simpa [hx] using h.length_eq.symm)
      subst xs
      subst ys
      simpa only [sub_self] using (level R L 0).zero_mem
    | succ n =>
      have ht : xs.length ≤ n + 1 := by simpa using hn
      simpa only [envelopingWord_cons, ← mul_sub, Nat.add_comm 1 n] using
        mul_mem R L (iota_mem R L x) (ih n ht)
  | swap x y xs =>
    have he : envelopingWord R L (y :: x :: xs) - envelopingWord R L (x :: y :: xs) =
        envelopingWord R L (⁅y, x⁆ :: xs) := by
      simp only [envelopingWord_cons]
      rw [LieHom.map_lie]
      change _ = (UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x -
        UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y) * _
      noncomm_ring
    rw [he]
    exact word_mem R L _ (by simp only [List.length_cons] at hn ⊢; omega)
  | @trans xs ys zs hxy hyz ihxy ihyz =>
    have hm : ys.length ≤ n + 1 := hxy.length_eq ▸ hn
    have hs := (level R L n).add_mem (ihxy n hn) (ihyz n hm)
    simpa only [sub_add_sub_cancel] using hs

end Parafree.Associative.EnvelopingFiltration
