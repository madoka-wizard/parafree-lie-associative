import Mathlib.Algebra.Lie.IdealOperations
import Mathlib.Data.ZMod.Basic

/-! Derived submodules under a surjective integral map to a Lie algebra over a
residue ring.  This includes lifting derived elements, not just mapping
bracket generators into the derived submodule. -/

noncomputable section
namespace Parafree.Lie

variable {L M : Type*} [LieRing L]
  [LieRing M] {p : ℕ} [LieAlgebra (ZMod p) M]

abbrev derivedSubmodule (R A : Type*) [CommRing R] [LieRing A] [LieAlgebra R A] :
    Submodule R A := (⁅(⊤ : LieIdeal R A), (⊤ : LieIdeal R A)⁆).toSubmodule

variable (f : L →ₗ⁅ℤ⁆ M)

theorem integralMap_mem_derived {x : L} (hx : x ∈ derivedSubmodule ℤ L) :
    f x ∈ derivedSubmodule (ZMod p) M := by
  rw [derivedSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
  refine Submodule.span_induction
    (p := fun x _ => f x ∈ derivedSubmodule (ZMod p) M) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, _, b, _, rfl⟩
    rw [LieHom.map_lie]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact (derivedSubmodule (ZMod p) M).add_mem ha hb
  · intro c a _ ha
    rw [map_smul]
    exact (derivedSubmodule (ZMod p) M).toAddSubgroup.zsmul_mem ha c

theorem integralMap_derived_lift (hf : Function.Surjective f) {y : M}
    (hy : y ∈ derivedSubmodule (ZMod p) M) :
    ∃ x ∈ derivedSubmodule ℤ L, f x = y := by
  rw [derivedSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hy
  refine Submodule.span_induction
    (p := fun y _ => ∃ x ∈ derivedSubmodule ℤ L, f x = y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, _, b, _, rfl⟩
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    exact ⟨⁅x, y⁆, LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _),
      f.map_lie x y⟩
  · exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  · rintro a b _ _ ⟨x, hx, he⟩ ⟨y, hy, hh⟩
    exact ⟨x + y, (derivedSubmodule ℤ L).add_mem hx hy,
      (map_add f x y).trans (congrArg₂ (· + ·) he hh)⟩
  · rintro c a _ ⟨x, hx, he⟩
    refine ⟨(c.cast : ℤ) • x, (derivedSubmodule ℤ L).smul_mem _ hx, ?_⟩
    rw [map_smul, he, ← Int.cast_smul_eq_zsmul (ZMod p), ZMod.intCast_zmod_cast]

/-- The map on abelianizations induced by an integral Lie homomorphism. -/
def integralAbelianMap : (L ⧸ derivedSubmodule ℤ L) →ₗ[ℤ]
    (M ⧸ derivedSubmodule (ZMod p) M) :=
  (derivedSubmodule ℤ L).liftQ
    (((derivedSubmodule (ZMod p) M).mkQ.restrictScalars ℤ).comp f.toLinearMap) (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr (integralMap_mem_derived f hx))

@[simp] theorem integralAbelianMap_mk (x : L) :
    integralAbelianMap (p := p) f (Submodule.Quotient.mk x) =
      (derivedSubmodule (ZMod p) M).mkQ (f x) := rfl

theorem integralAbelianMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (integralAbelianMap (p := p) f) := by
  intro y
  obtain ⟨a, rfl⟩ := (derivedSubmodule (ZMod p) M).mkQ_surjective y
  obtain ⟨b, rfl⟩ := hf a
  exact ⟨Submodule.Quotient.mk b, rfl⟩

/-- If an onto Lie map has exactly the scalar multiples as kernel, the same
is true after abelianization. The forward implication lifts a derived element,
so it does not assume flatness of the residue ring. -/
theorem integralAbelianMap_eq_zero_iff (hf : Function.Surjective f)
    (hker : ∀ x : L, f x = 0 ↔ ∃ y : L, (p : ℤ) • y = x)
    (x : L ⧸ derivedSubmodule ℤ L) :
    integralAbelianMap (p := p) f x = 0 ↔ ∃ y : L ⧸ derivedSubmodule ℤ L, (p : ℤ) • y = x := by
  obtain ⟨a, rfl⟩ := (derivedSubmodule ℤ L).mkQ_surjective x
  constructor
  · intro hx
    have hderived : f a ∈ derivedSubmodule (ZMod p) M :=
      (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨b, hb, he⟩ := integralMap_derived_lift f hf hderived
    have hzero : f (a - b) = 0 := by rw [map_sub, he, sub_self]
    obtain ⟨c, hc⟩ := (hker (a - b)).mp hzero
    refine ⟨(derivedSubmodule ℤ L).mkQ c, ?_⟩
    change (p : ℤ) • (derivedSubmodule ℤ L).mkQ c = (derivedSubmodule ℤ L).mkQ a
    have hbzero : (derivedSubmodule ℤ L).mkQ b = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hb
    rw [← map_smul, hc, map_sub, hbzero, sub_zero]
  · rintro ⟨y, hy⟩
    rw [← hy, map_smul, ← Int.cast_smul_eq_zsmul (ZMod p)]
    simp

end Parafree.Lie
