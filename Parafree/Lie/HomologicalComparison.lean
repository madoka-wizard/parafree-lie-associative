import Parafree.Homology.ReducedExteriorExactness
import Parafree.Lie.NilpotentFixedPoint

/-! Lower-central comparison when the target has vanishing second CE homology.
Only an isomorphism on abelianizations is required of the chosen map. -/

noncomputable section
namespace Parafree.Lie

open LieRings.Homological.LieHomology
open Parafree.Homology.ReducedExterior

variable {R : Type*} [CommRing R]
variable {L M : Type*} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

theorem nilpotentMap_surjective_iff (f : L →ₗ⁅R⁆ M) (n : ℕ) :
    Function.Surjective (nilpotentMap f n) ↔
      ∀ y, ∃ x, y - f x ∈ lowerCentral R M n := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (quotientMk _ y)
    obtain ⟨x, rfl⟩ := quotientMk_surjective _ x
    refine ⟨x, (quotientMk_eq_zero _ _).mp ?_⟩
    rw [map_sub, ← nilpotentMap_mk, hx, sub_self]
  · intro h y
    obtain ⟨y, rfl⟩ := quotientMk_surjective _ y
    obtain ⟨x, hx⟩ := h y
    refine ⟨quotientMk _ x, ?_⟩
    exact (sub_eq_zero.mp (by
      rw [nilpotentMap_mk, ← map_sub]
      exact (quotientMk_eq_zero _ _).mpr hx)).symm

theorem nilpotentMap_injective_iff (f : L →ₗ⁅R⁆ M) (n : ℕ) :
    Function.Injective (nilpotentMap f n) ↔
      ∀ x, f x ∈ lowerCentral R M n → x ∈ lowerCentral R L n := by
  constructor
  · intro h x hx
    apply (quotientMk_eq_zero _ _).mp
    apply h
    rw [map_zero, nilpotentMap_mk]
    exact (quotientMk_eq_zero _ _).mpr hx
  · intro h x y hxy
    obtain ⟨x, rfl⟩ := quotientMk_surjective _ x
    obtain ⟨y, rfl⟩ := quotientMk_surjective _ y
    apply sub_eq_zero.mp
    rw [← map_sub, quotientMk_eq_zero]
    apply h
    apply (quotientMk_eq_zero _ _).mp
    rw [map_sub, map_sub]
    exact sub_eq_zero.mpr hxy

/-- Surjectivity on abelianization gives surjectivity on every nilpotent quotient. -/
theorem nilpotentMap_surjective_of_abelian (f : L →ₗ⁅R⁆ M)
    (h : Function.Surjective (nilpotentMap f 1)) (n : ℕ) :
    Function.Surjective (nilpotentMap f n) := by
  have h1 := (nilpotentMap_surjective_iff f 1).mp h
  apply (nilpotentMap_surjective_iff f n).mpr
  induction n with
  | zero => intro y; exact ⟨0, LieSubmodule.mem_top _⟩
  | succ n ih =>
    have hderived : ∀ z ∈ lowerCentral R M 1,
        ∃ x, z - f x ∈ lowerCentral R M (n + 1) := by
      intro z hz
      change z ∈ (⁅(⊤ : LieIdeal R M), (⊤ : LieIdeal R M)⁆).toSubmodule at hz
      rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hz
      refine Submodule.span_induction (p := fun z _ =>
        ∃ x, z - f x ∈ lowerCentral R M (n + 1)) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨a, _, b, _, rfl⟩
        obtain ⟨x, hx⟩ := ih a
        obtain ⟨y, hy⟩ := ih b
        refine ⟨⁅x, y⁆, ?_⟩
        rw [f.map_lie]
        exact lie_sub_lie_mem_lowerCentral_succ n hx hy
      · exact ⟨0, by simp⟩
      · rintro a b _ _ ⟨x, hx⟩ ⟨y, hy⟩
        refine ⟨x + y, ?_⟩
        simpa only [map_add, add_sub_add_comm] using
          (lowerCentral R M (n + 1)).add_mem hx hy
      · rintro r a _ ⟨x, hx⟩
        refine ⟨r • x, ?_⟩
        simpa only [map_smul, smul_sub] using
          (lowerCentral R M (n + 1)).smul_mem r hx
    intro y
    obtain ⟨x, hx⟩ := h1 y
    obtain ⟨z, hz⟩ := hderived (y - f x) hx
    refine ⟨x + z, ?_⟩
    simpa only [map_add, sub_add_eq_sub_sub] using hz

/-- One induction step, proved on reduced exterior-square representatives. -/
theorem nilpotentMap_injective_succ (f : L →ₗ⁅R⁆ M)
    [Subsingleton (Homology (R := R) (L := M) 2)]
    (h1 : Function.Injective (nilpotentMap f 1)) (n : ℕ)
    (hn : Function.Bijective (nilpotentMap f n)) :
    Function.Injective (nilpotentMap f (n + 1)) := by
  apply (nilpotentMap_injective_iff f (n + 1)).mpr
  intro x hx
  have hx1 : x ∈ lowerCentral R L 1 :=
    (nilpotentMap_injective_iff f 1).mp h1 x
      (LieModule.antitone_lowerCentralSeries R M M (Nat.le_add_left 1 n) hx)
  obtain ⟨a, ha⟩ := exists_bracket hx1
  have hfx : f x ∈ (relationWedges R (quotientMk (lowerCentral R M n))).map
      (reducedBracket R M) := by
    rw [bracket_relationWedges]
    simpa only [lowerCentral, LieModule.lowerCentralSeries_succ] using hx
  obtain ⟨b, hb, hbr⟩ := hfx
  have hfa : reducedExteriorMap (R := R) f a = b := by
    apply bracket_injective_of_homologyTwo_zero
    exact (LinearMap.congr_fun (reducedBracket_natural R f) a).symm.trans
      ((congrArg f ha).trans hbr.symm)
  have hzero : reducedExteriorMap (R := R) (quotientMk (lowerCentral R M n))
      (reducedExteriorMap (R := R) f a) = 0 := by
    rw [hfa]
    exact (map_eq_zero_iff _ (quotientMk_surjective _) b).mpr hb
  have hcomm : (quotientMk (lowerCentral R M n)).comp f =
      (nilpotentMap f n).comp (quotientMk (lowerCentral R L n)) := rfl
  rw [← LinearMap.comp_apply, ← map_comp, hcomm, map_comp,
    LinearMap.comp_apply] at hzero
  have hazero : reducedExteriorMap (R := R) (quotientMk (lowerCentral R L n)) a = 0 :=
    (map_bijective (nilpotentMap f n) hn).1 (hzero.trans ((reducedExteriorMap (R := R) (nilpotentMap f n)).map_zero).symm)
  have hamem := (map_eq_zero_iff _ (quotientMk_surjective _) a).mp hazero
  have hbrmem : reducedBracket R L a ∈
      (relationWedges R (quotientMk (lowerCentral R L n))).map (reducedBracket R L) :=
    ⟨a, hamem, rfl⟩
  rw [bracket_relationWedges, ha] at hbrmem
  simpa only [lowerCentral, LieModule.lowerCentralSeries_succ] using hbrmem

/-- A version of the lower-central comparison theorem specialized to an acyclic
second-homology target. It holds over any commutative base ring. -/
theorem isParaEquivalence_of_homologyTwo_zero (f : L →ₗ⁅R⁆ M)
    [Subsingleton (Homology (R := R) (L := M) 2)]
    (h1 : Function.Bijective (nilpotentMap f 1)) : IsParaEquivalence f := by
  intro n
  refine ⟨?_, nilpotentMap_surjective_of_abelian f h1.2 n⟩
  induction n with
  | zero =>
    apply (nilpotentMap_injective_iff f 0).mpr
    intro x _
    exact LieSubmodule.mem_top x
  | succ n ih =>
    exact nilpotentMap_injective_succ f h1.1 n
      ⟨ih, nilpotentMap_surjective_of_abelian f h1.2 n⟩

end Parafree.Lie
