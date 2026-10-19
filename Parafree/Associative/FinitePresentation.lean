import Parafree.Associative.Quotient
import Mathlib.Algebra.FreeAlgebra

/-! Finite presentations for associative, possibly noncommutative algebras.
The relation ideal is generated as a two-sided ideal. -/
noncomputable section
namespace Parafree.Associative

variable (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A]

/-- Finitely many free algebra generators and finitely many two-sided relators. -/
def IsFinitelyPresented : Prop :=
  ∃ (n : ℕ) (f : FreeAlgebra k (Fin n) →ₐ[k] A), Function.Surjective f ∧
    ∃ s : Finset (FreeAlgebra k (Fin n)), RingHom.ker f = twoSidedSpan (s : Set _)

variable {k A}

/-- Finite generation of the relation ideal is independent of the chosen
finite generating presentation. This is the elementary Tietze argument. -/
theorem IsFinitelyPresented.finite_relations (hA : IsFinitelyPresented k A)
    {n : ℕ} (f : FreeAlgebra k (Fin n) →ₐ[k] A) (hf : Function.Surjective f) :
    ∃ s : Finset (FreeAlgebra k (Fin n)), RingHom.ker f = twoSidedSpan (s : Set _) := by
  classical
  obtain ⟨m,g,hg,r,hr⟩ := hA
  let u : FreeAlgebra k (Fin m) →ₐ[k] FreeAlgebra k (Fin n) :=
    FreeAlgebra.lift k (fun i => (hf (g (FreeAlgebra.ι k i))).choose)
  let v : FreeAlgebra k (Fin n) →ₐ[k] FreeAlgebra k (Fin m) :=
    FreeAlgebra.lift k (fun i => (hg (f (FreeAlgebra.ι k i))).choose)
  have hu : f.comp u = g := by
    apply FreeAlgebra.hom_ext
    funext i
    change f (u (FreeAlgebra.ι k i)) = _
    rw [show u (FreeAlgebra.ι k i) = (hf (g (FreeAlgebra.ι k i))).choose from
      FreeAlgebra.lift_ι_apply _ _]
    exact (hf _).choose_spec
  have hv : g.comp v = f := by
    apply FreeAlgebra.hom_ext
    funext i
    change g (v (FreeAlgebra.ι k i)) = _
    rw [show v (FreeAlgebra.ι k i) = (hg (f (FreeAlgebra.ι k i))).choose from
      FreeAlgebra.lift_ι_apply _ _]
    exact (hg _).choose_spec
  have hu' (y) : f (u y) = g y := AlgHom.congr_fun hu y
  have hv' (x) : g (v x) = f x := AlgHom.congr_fun hv x
  let d (i : Fin n) := FreeAlgebra.ι k i - u (v (FreeAlgebra.ι k i))
  let s := r.image u ∪ Finset.univ.image d
  let J : Ideal (FreeAlgebra k (Fin n)) := twoSidedSpan (s : Set _)
  let q : FreeAlgebra k (Fin n) →ₐ[k] (FreeAlgebra k (Fin n) ⧸ J) :=
    Ideal.Quotient.mkₐ k J
  have hq : q = (q.comp u).comp v := by
    apply FreeAlgebra.hom_ext
    funext i
    apply sub_eq_zero.mp
    change q (FreeAlgebra.ι k i) - q (u (v (FreeAlgebra.ι k i))) = 0
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply subset_twoSidedSpan
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hru : RingHom.ker g ≤ RingHom.ker (q.comp u) := by
    rw [hr]
    apply twoSidedSpan_le
    intro x hx
    change q (u x) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply subset_twoSidedSpan
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  refine ⟨s, le_antisymm ?_ ?_⟩
  · intro x hx
    have hvg : v x ∈ RingHom.ker g := by
      change g (v x) = 0
      exact (AlgHom.congr_fun hv x).trans hx
    have hz := hru hvg
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q x = 0
    rw [hq]
    exact hz
  · apply twoSidedSpan_le
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      change f (u y) = 0
      rw [hu' y]
      exact (hr.symm ▸ subset_twoSidedSpan hy : y ∈ RingHom.ker g)
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      change f (FreeAlgebra.ι k i - u (v (FreeAlgebra.ι k i))) = 0
      rw [map_sub, hu', hv', sub_self]

end Parafree.Associative
