import Mathlib.Algebra.Lie.Ideal

/-! Membership of scaled ideal elements from their generators. This lemma
requires neither ideal-power filtrations nor a chosen inverse scalar. -/
namespace Parafree.Lie
variable {R S F A J : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [LieRing F] [LieAlgebra R F] [LieRing A] [LieAlgebra R A] [LieAlgebra S A]
  [IsScalarTower R S A]

/-- A subalgebra containing the ambient image and the scaled relators contains
all scaled elements of their ideal. -/
theorem smul_map_mem_of_lieSpan (ι : F →ₗ⁅R⁆ A) (b : S) (H : LieSubalgebra R A)
    (r : J → F) (hF : ∀ x, ι x ∈ H) (hrH : ∀ j, b • ι (r j) ∈ H)
    {x : F} (hx : x ∈ LieSubmodule.lieSpan R F (Set.range r)) : b • ι x ∈ H := by
  refine LieSubmodule.lieSpan_induction (R := R) (L := F)
    (p := fun x _ => b • ι x ∈ H) ?_ ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j,rfl⟩; exact hrH j
  · simpa only [map_zero,smul_zero] using H.zero_mem
  · intro x y _ _ hx hy; simpa only [map_add,smul_add] using H.add_mem hx hy
  · intro r x _ hx
    rw [map_smul,smul_comm]
    exact H.smul_mem r hx
  · intro x y _ hy
    rw [LieHom.map_lie,← lie_smul]
    exact H.lie_mem (hF x) hy

end Parafree.Lie
