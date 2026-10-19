import Parafree.Lie.Quotient
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.IdealOperations

/-! Finite Lie presentations and the module of central relation classes. -/
noncomputable section
namespace Parafree.Lie

/-- A finite presentation means finitely many free generators and finitely many
ideal relators. It does not assert finite generation of the relation ideal as
an underlying module. -/
def IsFinitelyPresented (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] : Prop :=
  ∃ (n : ℕ) (p : FreeLieAlgebra R (Fin n) →ₗ⁅R⁆ L), Function.Surjective p ∧
    ∃ (m : ℕ) (r : Fin m → FreeLieAlgebra R (Fin n)),
      p.ker = LieSubmodule.lieSpan R (FreeLieAlgebra R (Fin n)) (Set.range r)

namespace CentralRelations
variable {R : Type*} [CommRing R] {F : Type*} [LieRing F] [LieAlgebra R F]
variable (I : LieIdeal R F)

abbrev denominator : LieIdeal R F := ⁅(⊤ : LieIdeal R F),I⁆
abbrev Quotient := F ⧸ denominator I
def project : F →ₗ⁅R⁆ Quotient I := quotientMk (denominator I)
def image : Submodule R (Quotient I) := I.toSubmodule.map (project I).toLinearMap

@[simp] theorem project_zero_iff (x : F) : project I x = 0 ↔ x ∈ denominator I :=
  quotientMk_eq_zero _ _

theorem image_eq_span {ι : Type*} (r : ι → F)
    (hr : I = LieSubmodule.lieSpan R F (Set.range r)) :
    image I = Submodule.span R (Set.range (fun i => project I (r i))) := by
  apply le_antisymm
  · rintro _ ⟨y,hy,rfl⟩
    rw [hr] at hy
    induction hy using LieSubmodule.lieSpan_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩ := hy
      exact Submodule.subset_span (Set.mem_range_self i)
    | zero => simpa only [map_zero] using (Submodule.zero_mem _)
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul r y hy ih => simpa only [map_smul] using Submodule.smul_mem _ r ih
    | lie x y hy ih =>
      have hxy : project I ⁅x,y⁆ = 0 := (project_zero_iff I _).mpr
        (LieSubmodule.lie_mem_lie (by trivial) (hr.symm ▸ hy))
      change project I ⁅x,y⁆ ∈ Submodule.span R (Set.range (fun i => project I (r i)))
      rw [hxy]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨r i, hr.symm ▸ LieSubmodule.subset_lieSpan (Set.mem_range_self i), rfl⟩

theorem finite_image {ι : Type*} [Finite ι] (r : ι → F)
    (hr : I = LieSubmodule.lieSpan R F (Set.range r)) : Module.Finite R (image I) := by
  apply Module.Finite.of_fg
  rw [image_eq_span I r hr]
  exact Submodule.fg_span (Set.finite_range _)

end CentralRelations
end Parafree.Lie
