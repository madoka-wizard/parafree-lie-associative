import Mathlib.Algebra.Lie.Ideal
import Mathlib.Data.ZMod.Basic

/-! Generation of ideals commutes with a surjective integral Lie map to a
residue-ring Lie algebra. Both directions are constructive on ideal spans;
no freeness, saturation, or primality assumption is needed. -/

noncomputable section
namespace Parafree.Lie

variable {L M ι : Type*} [LieRing L] [LieRing M]
  {n : ℕ} [LieAlgebra (ZMod n) M]
variable (f : L →ₗ⁅ℤ⁆ M) (r : ι → L) (s : ι → M) (hrs : ∀ i, f (r i) = s i)
include hrs

theorem integralMap_mem_lieSpan {x : L}
    (hx : x ∈ LieSubmodule.lieSpan ℤ L (Set.range r)) :
    f x ∈ LieSubmodule.lieSpan (ZMod n) M (Set.range s) := by
  let J := LieSubmodule.lieSpan (ZMod n) M (Set.range s)
  refine LieSubmodule.lieSpan_induction (R := ℤ) (L := L)
    (p := fun x _ => f x ∈ J) ?_ ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    rw [hrs]
    exact LieSubmodule.subset_lieSpan (Set.mem_range_self i)
  · change f 0 ∈ J
    rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact J.add_mem ha hb
  · intro c a _ ha
    rw [map_smul]
    exact J.toSubmodule.toAddSubgroup.zsmul_mem ha c
  · intro a b _ hb
    rw [LieHom.map_lie]; exact J.lie_mem hb

/-- Every element of the target ideal lifts to the source ideal, provided
that the ambient map is onto and maps the specified generators correctly. -/
theorem integralMap_lieSpan_lift (hf : Function.Surjective f) {y : M}
    (hy : y ∈ LieSubmodule.lieSpan (ZMod n) M (Set.range s)) :
    ∃ x : LieSubmodule.lieSpan ℤ L (Set.range r), f x = y := by
  let I := LieSubmodule.lieSpan ℤ L (Set.range r)
  refine LieSubmodule.lieSpan_induction (R := ZMod n) (L := M)
    (p := fun y _ => ∃ x : I, f x = y) ?_ ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨i, rfl⟩
    exact ⟨⟨r i, LieSubmodule.subset_lieSpan (Set.mem_range_self i)⟩, hrs i⟩
  · exact ⟨0, map_zero _⟩
  · rintro a b _ _ ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, (map_add f (x : L) (y : L)).trans (congrArg₂ (· + ·) hx hy)⟩
  · rintro c a _ ⟨x, hx⟩
    refine ⟨(c.cast : ℤ) • x, ?_⟩
    change f ((c.cast : ℤ) • (x : L)) = c • a
    rw [map_smul, hx, ← Int.cast_smul_eq_zsmul (ZMod n), ZMod.intCast_zmod_cast]
  · rintro a b _ ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf a
    refine ⟨⟨⁅x, (y : L)⁆, I.lie_mem y.property⟩, ?_⟩
    rw [LieHom.map_lie, hy]

end Parafree.Lie
