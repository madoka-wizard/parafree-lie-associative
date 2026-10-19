import Parafree.Upstream.CE

/-! Transport of the actual CE homology along Lie algebra equivalences. -/

namespace Parafree.Homology

open CategoryTheory LieRings.Homological.LieHomology

universe u v

variable {R : Type u} [CommRing R]
variable {L M : Type v} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

noncomputable def lieEquivHomologyIso (e : L ≃ₗ⁅R⁆ M) (n : ℕ) :
    homology (R := R) (L := L) n ≅ homology (R := R) (L := M) n where
  hom := homologyMap e.toLieHom n
  inv := homologyMap e.symm.toLieHom n
  hom_inv_id := by
    rw [← homologyMap_comp]
    have h : e.symm.toLieHom.comp e.toLieHom = LieHom.id := by
      apply LieHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [h, homologyMap_id]
  inv_hom_id := by
    rw [← homologyMap_comp]
    have h : e.toLieHom.comp e.symm.toLieHom = LieHom.id := by
      apply LieHom.ext
      intro x
      exact e.apply_symm_apply x
    rw [h, homologyMap_id]

noncomputable def lieEquivHomology (e : L ≃ₗ⁅R⁆ M) (n : ℕ) :
    Homology (R := R) (L := L) n ≃ₗ[R] Homology (R := R) (L := M) n :=
  (lieEquivHomologyIso e n).toLinearEquiv

end Parafree.Homology
