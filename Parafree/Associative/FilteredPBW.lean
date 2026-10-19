import Parafree.Associative.EnvelopingFiltration
import LieRings.Plotkin.GenericPBW

/-!
# PBW respects the word filtration

The intrinsic filtration by word length is exactly the span of ordered PBW
monomials of bounded total degree. The proof collects words modulo lower
filtration terms, using permutations and induction on length. It does not access
private details of the upstream Cartan--Eilenberg proof of PBW.
-/

noncomputable section

namespace Parafree.Associative.FilteredPBW

open LieRings LieRings.PBW EnvelopingFiltration

variable {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (b : Module.Basis ι R L)

def basisWordSpan (n : ℕ) : Submodule R (UEA R L) :=
  Submodule.span R {a | ∃ xs : List ι, xs.length ≤ n ∧ envelopingWord R L (xs.map b) = a}

theorem basisWordSpan_mono : Monotone (basisWordSpan b) := by
  intro m n hmn
  apply Submodule.span_mono
  rintro a ⟨xs, hx, rfl⟩
  exact ⟨xs, hx.trans hmn, rfl⟩

theorem basis_iota_mul_mem {n : ℕ} {a : UEA R L} (ha : a ∈ basisWordSpan b n) (i : ι) :
    UniversalEnvelopingAlgebra.ι R (b i) * a ∈ basisWordSpan b (n + 1) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨xs, hx, rfl⟩ := ha
    exact Submodule.subset_span ⟨i :: xs, by simpa using hx, rfl⟩
  | zero => simp
  | add a c _ _ ha hc => simpa only [mul_add] using (basisWordSpan b _).add_mem ha hc
  | smul r a _ ha => simpa only [mul_smul_comm] using (basisWordSpan b _).smul_mem r ha

theorem word_mem_basisWordSpan (xs : List L) :
    envelopingWord R L xs ∈ basisWordSpan b xs.length := by
  induction xs with
  | nil => exact Submodule.subset_span ⟨[], le_refl 0, rfl⟩
  | cons x xs ih =>
    have hx : x ∈ Submodule.span R (Set.range b) := b.span_eq.symm ▸ Submodule.mem_top
    simp only [envelopingWord_cons, List.length_cons]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact basis_iota_mul_mem b ih i
    | zero => simp
    | add x y _ _ hx hy =>
      simpa only [map_add, add_mul] using (basisWordSpan b _).add_mem hx hy
    | smul r x _ hx =>
      simpa only [map_smul, smul_mul_assoc] using (basisWordSpan b _).smul_mem r hx

theorem level_eq_basisWordSpan (n : ℕ) : level R L n = basisWordSpan b n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨xs, hx, rfl⟩
    exact basisWordSpan_mono b hx (word_mem_basisWordSpan b xs)
  · apply Submodule.span_le.mpr
    rintro a ⟨xs, hx, rfl⟩
    exact word_mem R L _ (by simpa using hx)

variable [LinearOrder ι]

def orderedSpan (n : ℕ) : Submodule R (UEA R L) :=
  Submodule.span R {a | ∃ e : ι →₀ ℕ, e.degree ≤ n ∧ orderedMonomial R L ι b e = a}

theorem orderedSpan_mono : Monotone (orderedSpan b) := by
  intro m n hmn
  apply Submodule.span_mono
  rintro a ⟨e, he, rfl⟩
  exact ⟨e, he.trans hmn, rfl⟩

theorem orderedSpan_le_level (n : ℕ) : orderedSpan b n ≤ level R L n := by
  apply Submodule.span_le.mpr
  rintro a ⟨e, he, rfl⟩
  have hlen : ((e.toMultiset.sort (· ≤ ·)).map b).length = e.degree := by
    simp [Finsupp.degree, Finsupp.sum]
  convert word_mem R L ((e.toMultiset.sort (· ≤ ·)).map b) (hlen.trans_le he) using 1
  simp only [orderedMonomial, envelopingWord, List.map_map, Function.comp_def]

theorem basisWord_sub_ordered (xs : List ι) (n : ℕ) (hn : xs.length ≤ n + 1) :
    envelopingWord R L (xs.map b) - orderedMonomial R L ι b (xs : Multiset ι).toFinsupp ∈
      level R L n := by
  have h := perm_sub_mem R L ((List.mergeSort_perm xs (· ≤ ·)).symm.map b) n
    (by simpa using hn)
  simpa [orderedMonomial, envelopingWord, List.map_map, Function.comp_def] using h

/-- Collection never increases the maximal word length. -/
theorem level_eq_orderedSpan (n : ℕ) : level R L n = orderedSpan b n := by
  apply le_antisymm ?_ (orderedSpan_le_level b n)
  induction n with
  | zero =>
    apply Submodule.span_le.mpr
    rintro a ⟨xs, hx, rfl⟩
    have hxs : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hx)
    subst xs
    exact Submodule.subset_span ⟨0, by simp, by simp⟩
  | succ n ih =>
    rw [level_eq_basisWordSpan b]
    apply Submodule.span_le.mpr
    rintro a ⟨xs, hx, rfl⟩
    have hd : ((xs : Multiset ι).toFinsupp).degree = xs.length :=
      Multiset.toFinsupp_sum_eq (xs : Multiset ι)
    have hord : orderedMonomial R L ι b (xs : Multiset ι).toFinsupp ∈ orderedSpan b (n + 1) :=
      Submodule.subset_span ⟨_, hd.trans_le hx, rfl⟩
    have hdiff := orderedSpan_mono b (Nat.le_succ n) (ih (basisWord_sub_ordered b xs n hx))
    simpa only [sub_add_cancel] using (orderedSpan b (n + 1)).add_mem hdiff hord

variable (R ι) in
def polynomialLevel (n : ℕ) : Submodule R (MvPolynomial ι R) :=
  Submodule.span R {p | ∃ e : ι →₀ ℕ, e.degree ≤ n ∧ MvPolynomial.monomial e 1 = p}

/-- The PBW map identifies bounded-degree polynomials with the intrinsic word
filtration, in every rank and characteristic. -/
theorem map_polynomialLevel (n : ℕ) :
    (polynomialLevel R ι n).map (orderedPBWMap R L ι b) = level R L n := by
  rw [level_eq_orderedSpan b, polynomialLevel, Submodule.map_span]
  apply congrArg (Submodule.span R)
  ext a
  constructor
  · rintro ⟨p, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, by simp⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨MvPolynomial.monomial e 1, ⟨e, he, rfl⟩, by simp⟩

def equiv : MvPolynomial ι R ≃ₗ[R] UEA R L :=
  LinearEquiv.ofBijective (orderedPBWMap R L ι b) (freeModulePBW_commRing L ι b)

theorem equiv_mem_level_iff (n : ℕ) (p : MvPolynomial ι R) :
    equiv b p ∈ level R L n ↔ p ∈ polynomialLevel R ι n := by
  rw [← map_polynomialLevel b]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqp : q = p := (equiv b).injective heq
    exact hqp ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

omit [LinearOrder ι] in
theorem polynomialLevel_eq_restrictTotalDegree (n : ℕ) :
    polynomialLevel R ι n = MvPolynomial.restrictTotalDegree ι R n := by
  rw [polynomialLevel, MvPolynomial.restrictTotalDegree, MvPolynomial.restrictSupport_eq_span]
  rfl

omit [LinearOrder ι] in
theorem mem_polynomialLevel_iff (n : ℕ) (p : MvPolynomial ι R) :
    p ∈ polynomialLevel R ι n ↔ p.totalDegree ≤ n := by
  rw [polynomialLevel_eq_restrictTotalDegree, MvPolynomial.mem_restrictTotalDegree]

theorem basis_mul_ordered_sub_mem (i : ι) (e : ι →₀ ℕ) :
    UniversalEnvelopingAlgebra.ι R (b i) * orderedMonomial R L ι b e -
      orderedMonomial R L ι b (Finsupp.single i 1 + e) ∈ level R L e.degree := by
  let xs := e.toMultiset.sort (· ≤ ·)
  have hlen : xs.length = e.degree := by simp [xs, Finsupp.degree, Finsupp.sum]
  have he : ((i :: xs : List ι) : Multiset ι).toFinsupp = Finsupp.single i 1 + e := by
    change (i ::ₘ (xs : Multiset ι)).toFinsupp = _
    rw [← Multiset.singleton_add, map_add]
    simp [xs]
  have h := basisWord_sub_ordered b (i :: xs) e.degree (by simp [hlen])
  rw [he] at h
  simpa only [List.map_cons, envelopingWord_cons, orderedMonomial, envelopingWord,
    List.map_map, Function.comp_def, xs] using h

/-- The leading term of left multiplication by a basis vector is multiplication
by its polynomial variable; the error loses one total filtration degree. -/
theorem basis_left_error_mem (i : ι) (n : ℕ) {p : MvPolynomial ι R}
    (hp : p ∈ polynomialLevel R ι n) :
    UniversalEnvelopingAlgebra.ι R (b i) * equiv b p - equiv b (MvPolynomial.X i * p) ∈
      level R L n := by
  let T : MvPolynomial ι R →ₗ[R] UEA R L :=
    (LinearMap.mulLeft R (UniversalEnvelopingAlgebra.ι R (b i))).comp (equiv b).toLinearMap -
      (equiv b).toLinearMap.comp (LinearMap.mulLeft R (MvPolynomial.X i))
  have hT : polynomialLevel R ι n ≤ (level R L n).comap T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    change T (MvPolynomial.monomial e 1) ∈ level R L n
    have h := monotone R L he (basis_mul_ordered_sub_mem b i e)
    simpa [T, equiv, MvPolynomial.X, MvPolynomial.monomial_mul] using h
  exact hT hp

theorem left_error_mem (x : L) (n : ℕ) {p : MvPolynomial ι R}
    (hp : p ∈ polynomialLevel R ι n) :
    UniversalEnvelopingAlgebra.ι R x * equiv b p - equiv b (basisPolynomial R L ι b x * p) ∈
      level R L n := by
  have hx : x ∈ Submodule.span R (Set.range b) := b.span_eq.symm ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa only [basisPolynomial_basis] using basis_left_error_mem b i n hp
  | zero => simp
  | add x y _ _ hx hy =>
    have h := (level R L n).add_mem hx hy
    simpa only [map_add, add_mul, add_sub_add_comm] using h
  | smul r x _ hx =>
    have h := (level R L n).smul_mem r hx
    simpa only [map_smul, smul_mul_assoc, smul_sub] using h

/-- The same leading-term estimate in PBW coordinates, ready to use on the
coefficient factor of a filtered Chevalley--Eilenberg complex. -/
theorem coordinate_left_error_mem (x : L) (n : ℕ) {p : MvPolynomial ι R}
    (hp : p ∈ polynomialLevel R ι n) :
    (equiv b).symm (UniversalEnvelopingAlgebra.ι R x * equiv b p) - basisPolynomial R L ι b x * p ∈
      polynomialLevel R ι n := by
  rw [← equiv_mem_level_iff b, map_sub, LinearEquiv.apply_symm_apply]
  exact left_error_mem b x n hp

end Parafree.Associative.FilteredPBW
