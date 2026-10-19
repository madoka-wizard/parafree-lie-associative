import Parafree.Linear.ModScalar
import Parafree.Linear.CommonPresentation

/-! Reduction modulo a scalar commutes with a module quotient, with a
representative formula. No flatness or basis hypothesis is needed. -/

noncomputable section
namespace Parafree.Linear.ModScalar

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (r : R) (P : Submodule R M)

def quotientReduction : M →ₗ[R] Quotient r (M ⧸ P) :=
  (mk r (M ⧸ P)).comp P.mkQ

theorem quotientReduction_surjective : Function.Surjective (quotientReduction r P) :=
  (mk_surjective r (M ⧸ P)).comp P.mkQ_surjective

theorem quotientReduction_ker : LinearMap.ker (quotientReduction r P) = P ⊔ multiples r M := by
  ext x
  constructor
  · intro hx
    change mk r (M ⧸ P) (P.mkQ x) = 0 at hx
    obtain ⟨y, hy⟩ := (mk_eq_zero r (M ⧸ P) _).mp hx
    obtain ⟨a, rfl⟩ := P.mkQ_surjective y
    have h : x - r • a ∈ P := by
      apply (Submodule.Quotient.eq P).mp
      exact hy.symm.trans (map_smul P.mkQ r a).symm
    exact Submodule.mem_sup.mpr ⟨x - r • a, h, r • a, ⟨a, rfl⟩, sub_add_cancel _ _⟩
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, ⟨c, rfl⟩, rfl⟩
    change mk r (M ⧸ P) (P.mkQ (a + r • c)) = 0
    have hzero : P.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero P).mpr ha
    rw [map_add, map_smul, map_add, hzero,
      map_zero, zero_add, mk_smul_self]

/-- The two standard presentations of reduction of a quotient. -/
def quotientReductionEquiv : Quotient r (M ⧸ P) ≃ₗ[R] M ⧸ (P ⊔ multiples r M) :=
  equivOfCommonPresentation (quotientReduction r P) (P ⊔ multiples r M).mkQ
    (quotientReduction_surjective r P) (P ⊔ multiples r M).mkQ_surjective
    ((quotientReduction_ker r P).trans (Submodule.ker_mkQ _).symm)

theorem quotientReductionEquiv_mk (x : M) :
    quotientReductionEquiv r P (mk r (M ⧸ P) (P.mkQ x)) =
      (P ⊔ multiples r M).mkQ x :=
  equivOfCommonPresentation_apply _ _ _ _ _ x

end Parafree.Linear.ModScalar
