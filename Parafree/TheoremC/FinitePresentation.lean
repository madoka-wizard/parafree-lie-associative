import Parafree.TheoremC.ReducedDifferential
import Parafree.Associative.FinitePresentation

/-! Every defining relator has its own independent relation coordinate.
These coordinates rule out any finite presentation, over any nonzero base ring. -/
noncomputable section
namespace Parafree.TheoremC
open Parafree.Associative
variable (k : Type*) [CommRing k]

namespace RelationCoordinates
open PresentationComplex

def coordinates : fullIdeal k →ₗ[k] (ℕ →₀ A k) where
  toFun r := (D_mem_range k r.property).choose
  map_add' r s := by
    apply d₂_injective k
    rw [(D_mem_range k (r+s).property).choose_spec, map_add,
      (D_mem_range k r.property).choose_spec, (D_mem_range k s.property).choose_spec]
    exact map_add (D k) r.val s.val
  map_smul' a r := by
    apply d₂_injective k
    rw [(D_mem_range k (a • r).property).choose_spec,
      (d₂ k).map_smul_of_tower, (D_mem_range k r.property).choose_spec]
    exact map_smul (D k) a r.val

theorem d₂_coordinates (r : fullIdeal k) : d₂ k (coordinates k r) = D k r.val :=
  (D_mem_range k r.property).choose_spec

def reduced : fullIdeal k →ₗ[k] (ℕ →₀ k) :=
  (CoinvariantsFree.reduce (augmentation k) ℕ).comp (coordinates k)

theorem reduced_relator (n : ℕ) :
    reduced k ⟨relator k n, subset_twoSidedSpan ⟨n,rfl⟩⟩ = Finsupp.single n 1 := by
  have h : coordinates k ⟨relator k n, subset_twoSidedSpan ⟨n,rfl⟩⟩ =
      Finsupp.single n 1 := by
    apply d₂_injective k
    rw [d₂_coordinates]
    simp [d₂]
  simp [reduced, h]

theorem reduced_left (a : Free k) (r : fullIdeal k) :
    reduced k ⟨a*r.val, (fullIdeal k).mul_mem_left a r.property⟩ =
      freeAugmentation k a • reduced k r := by
  have h : coordinates k ⟨a*r.val, (fullIdeal k).mul_mem_left a r.property⟩ =
      toFull k a • coordinates k r := by
    apply d₂_injective k
    rw [d₂_coordinates, map_smul, d₂_coordinates, D_mul,
      show freeAugmentation k r.val = 0 from fullIdeal_le_augmentation k r.property,
      zero_smul, add_zero]
  simp only [reduced, LinearMap.comp_apply, h, CoinvariantsFree.reduce_smul,
    augmentation_toFull]

theorem reduced_right (a : Free k) (r : fullIdeal k) :
    reduced k ⟨r.val*a, (fullIdeal k).mul_mem_right a r.property⟩ =
      freeAugmentation k a • reduced k r := by
  have h : coordinates k ⟨r.val*a, (fullIdeal k).mul_mem_right a r.property⟩ =
      freeAugmentation k a • coordinates k r := by
    apply d₂_injective k
    rw [d₂_coordinates, (d₂ k).map_smul_of_tower, d₂_coordinates, D_mul,
      show toFull k r.val = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr r.property,
      zero_smul, zero_add]
  simp only [reduced, LinearMap.comp_apply, h, map_smul]

theorem not_finite_relations [Nontrivial k] :
    ¬ ∃ s : Finset (Free k), fullIdeal k = twoSidedSpan (s : Set _) := by
  classical
  rintro ⟨s,hs⟩
  have mem (r : Free k) (hr : r ∈ s) : r ∈ fullIdeal k :=
    hs.symm ▸ subset_twoSidedSpan hr
  let t : Finset (fullIdeal k) := s.attach.image (fun r => ⟨r.val, mem r.val r.property⟩)
  let support : Finset ℕ := t.biUnion (fun r => (reduced k r).support)
  let n := support.sup id + 1
  have hn : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    omega
  have generators (r : Free k) (hr : r ∈ s) : reduced k ⟨r,mem r hr⟩ n = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro h
    apply hn
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨r,mem r hr⟩, ?_, h⟩
    exact Finset.mem_image.mpr ⟨⟨r,hr⟩, Finset.mem_attach _ _, rfl⟩
  have all (r : Free k) (hr : r ∈ twoSidedSpan (s : Set _)) :
      ∀ h : r ∈ fullIdeal k, reduced k ⟨r,h⟩ n = 0 := by
    induction hr using TwoSidedIdeal.span_induction with
    | mem r hr => intro h; exact generators r hr
    | zero => intro h; exact congrArg (fun v : ℕ →₀ k => v n) (map_zero (reduced k))
    | add a b ha hb ih₁ ih₂ =>
      intro h
      have ha' : a ∈ fullIdeal k := hs.symm ▸ ha
      have hb' : b ∈ fullIdeal k := hs.symm ▸ hb
      change reduced k (⟨a,ha'⟩ + ⟨b,hb'⟩) n = 0
      rw [map_add (reduced k) _ _, Finsupp.add_apply, ih₁ ha', ih₂ hb', add_zero]
    | neg a ha ih =>
      intro h
      have ha' : a ∈ fullIdeal k := hs.symm ▸ ha
      change reduced k (-⟨a,ha'⟩) n = 0
      rw [map_neg, Finsupp.neg_apply, ih ha', neg_zero]
    | left_absorb a b hb ih =>
      intro h
      have hb' : b ∈ fullIdeal k := hs.symm ▸ hb
      rw [reduced_left k a ⟨b,hb'⟩, Finsupp.smul_apply, ih hb', smul_zero]
    | right_absorb b a ha ih =>
      intro h
      have ha' : a ∈ fullIdeal k := hs.symm ▸ ha
      rw [reduced_right k b ⟨a,ha'⟩, Finsupp.smul_apply, ih ha', smul_zero]
  have he : relator k n ∈ fullIdeal k := subset_twoSidedSpan ⟨n,rfl⟩
  have hz := all (relator k n) (hs ▸ he) he
  rw [reduced_relator, Finsupp.single_eq_same] at hz
  exact one_ne_zero hz

end RelationCoordinates

theorem not_finitelyPresented [Nontrivial k] : ¬ IsFinitelyPresented k (A k) := by
  intro h
  obtain ⟨s,hs⟩ := h.finite_relations (toFull k) (Ideal.Quotient.mkₐ_surjective k (fullIdeal k))
  apply RelationCoordinates.not_finite_relations k
  refine ⟨s, ?_⟩
  rw [← hs]
  ext x
  exact Ideal.Quotient.eq_zero_iff_mem.symm

end Parafree.TheoremC
