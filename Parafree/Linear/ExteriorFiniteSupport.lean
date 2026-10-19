import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Finite support in exterior powers of a free module

Every chain in the exterior power of a finitely supported function module comes
from a finite subset of its basis. The inclusions are split injections over any
commutative ring. This is the finite-support reduction used for resolutions of
free modules of arbitrary rank.
-/

noncomputable section

namespace Parafree.Linear.ExteriorFiniteSupport

open ExteriorAlgebra

variable (R σ : Type*) [CommRing R]

def inclusion (s : Finset σ) : (s →₀ R) →ₗ[R] (σ →₀ R) :=
  Finsupp.lmapDomain R R Subtype.val

def restriction (s : Finset σ) : (σ →₀ R) →ₗ[R] (s →₀ R) :=
  Finsupp.lcomapDomain Subtype.val Subtype.val_injective

@[simp] theorem restriction_inclusion (s : Finset σ) :
    (restriction R σ s).comp (inclusion R σ s) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact Finsupp.leftInverse_lcomapDomain_mapDomain
    (M := R) (R := R) (Subtype.val : s → σ) Subtype.val_injective v

theorem inclusion_restriction (s : Finset σ) (v : σ →₀ R) (hv : v.support ⊆ s) :
    inclusion R σ s (restriction R σ s v) = v := by
  apply Finsupp.mapDomain_comapDomain (Subtype.val : s → σ) Subtype.val_injective
  intro i hi
  exact ⟨⟨i, hv hi⟩, rfl⟩

def exteriorInclusion (s : Finset σ) (n : ℕ) :
    (⋀[R]^n (s →₀ R)) →ₗ[R] (⋀[R]^n (σ →₀ R)) :=
  exteriorPower.map n (inclusion R σ s)

theorem exteriorInclusion_injective (s : Finset σ) (n : ℕ) :
    Function.Injective (exteriorInclusion R σ s n) :=
  exteriorPower.map_injective (n := n) (restriction R σ s) (restriction_inclusion R σ s)

theorem range_mono {s t : Finset σ} (h : s ⊆ t) (n : ℕ) :
    (exteriorInclusion R σ s n).range ≤ (exteriorInclusion R σ t n).range := by
  let f : (s →₀ R) →ₗ[R] (t →₀ R) :=
    Finsupp.lmapDomain R R (fun i : s => ⟨i.1, h i.2⟩)
  have hf : (inclusion R σ t).comp f = inclusion R σ s := by
    ext i r
    simp [f, inclusion, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rintro _ ⟨x, rfl⟩
  refine ⟨exteriorPower.map n f x, ?_⟩
  change (exteriorPower.map n (inclusion R σ t)).comp (exteriorPower.map n f) x = _
  rw [← exteriorPower.map_comp, hf]
  rfl

theorem ranges_directed (n : ℕ) :
    Directed (· ≤ ·) (fun s : Finset σ => (exteriorInclusion R σ s n).range) := by
  classical
  intro s t
  exact ⟨s ∪ t, range_mono R σ Finset.subset_union_left n,
    range_mono R σ Finset.subset_union_right n⟩

/-- A single finite set supports an entire exterior chain, including sums of
wedges. No finiteness condition is imposed on the ambient basis. -/
theorem exists_lift (n : ℕ) (x : ⋀[R]^n (σ →₀ R)) :
    ∃ s : Finset σ, ∃ y : ⋀[R]^n (s →₀ R), exteriorInclusion R σ s n y = x := by
  classical
  let P := ⨆ s : Finset σ, (exteriorInclusion R σ s n).range
  have htop : P = ⊤ := by
    apply top_unique
    rw [← exteriorPower.ιMulti_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    let s := Finset.univ.biUnion (fun i : Fin n => (v i).support)
    let w : Fin n → (s →₀ R) := fun i => restriction R σ s (v i)
    have hw : (inclusion R σ s) ∘ w = v := by
      funext i
      apply inclusion_restriction
      exact Finset.subset_biUnion_of_mem (fun i : Fin n => (v i).support) (Finset.mem_univ i)
    apply Submodule.mem_iSup_of_mem s
    refine ⟨exteriorPower.ιMulti R n w, ?_⟩
    change exteriorPower.map n (inclusion R σ s) (exteriorPower.ιMulti R n w) = _
    rw [exteriorPower.map_apply_ιMulti, hw]
  have hx : x ∈ P := htop.symm ▸ Submodule.mem_top
  obtain ⟨s, y, hy⟩ := (Submodule.mem_iSup_of_directed _ (ranges_directed R σ n)).mp hx
  exact ⟨s, y, hy⟩

end Parafree.Linear.ExteriorFiniteSupport
