import Parafree.Lie.IntegralFreeModule
import Parafree.Lie.LowerCentral

/-!
# Free integral nilpotent quotients in countable rank

Truncated Magnus coordinates embed each nilpotent quotient in a countably
based free module. This avoids constructing an infinite homogeneous Hall
basis and uses no finiteness assumption on the number of generators.
-/

noncomputable section

namespace Parafree.Lie.FreeTruncation

open LieRings
open FreeLieDimension

variable (X : Type*)

private def wordProjection (n : ℕ) : (FreeMonoid X →₀ ℤ) →ₗ[ℤ] (FreeMonoid X →₀ ℤ) where
  toFun := Finsupp.filter (fun w : FreeMonoid X => w.length ≤ n)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

/-- Keep Magnus coordinates of word length at most the nilpotency class. -/
def coordinates (n : ℕ) : FreeLieAlgebra ℤ X →ₗ[ℤ] (FreeMonoid X →₀ ℤ) :=
  (wordProjection X n).comp
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap.comp
      (PBW.freeLieToFreeAlgebra ℤ X).toLinearMap)

theorem coordinates_eq_zero_iff (n : ℕ) (x : FreeLieAlgebra ℤ X) :
    coordinates X n x = 0 ↔ x ∈ lowerCentral ℤ (FreeLieAlgebra ℤ X) n := by
  have hhigh : coordinates X n x = 0 ↔
      PBW.freeLieToFreeAlgebra ℤ X x ∈ associativeHigh X (n + 1) := by
    constructor
    · intro hx w hw
      have hwne := Finsupp.mem_support_iff.mp hw
      change n + 1 ≤ w.length
      by_contra hlen
      have hle : w.length ≤ n := by omega
      have hz := congrArg (fun a : FreeMonoid X →₀ ℤ => a w) hx
      change (Finsupp.filter (fun w : FreeMonoid X => w.length ≤ n)
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid (PBW.freeLieToFreeAlgebra ℤ X x))) w = 0 at hz
      rw [Finsupp.filter_apply_pos (p := fun w : FreeMonoid X => w.length ≤ n) (f := _) hle] at hz
      exact hwne hz
    · intro hx
      ext w
      change (Finsupp.filter (fun w : FreeMonoid X => w.length ≤ n)
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid (PBW.freeLieToFreeAlgebra ℤ X x))) w = 0
      by_cases hw : w.length ≤ n
      · rw [Finsupp.filter_apply_pos (p := fun w : FreeMonoid X => w.length ≤ n) (f := _) hw]
        by_contra hne
        have hgt := hx (Finsupp.mem_support_iff.mpr hne)
        change n + 1 ≤ w.length at hgt
        omega
      · exact Finsupp.filter_apply_neg (p := fun w : FreeMonoid X => w.length ≤ n) (f := _) hw
  rw [hhigh]
  have hmem : (x ∈ lieHigh X (n + 1)) =
      (x ∈ lowerCentral ℤ (FreeLieAlgebra ℤ X) n) :=
    congrArg (fun P : Submodule ℤ (FreeLieAlgebra ℤ X) => x ∈ P)
      (lieHigh_eq_lowerCentralSeries X n)
  rw [← hmem]
  constructor
  · intro hx
    obtain ⟨p,rfl⟩ := Quot.mk_surjective x
    apply freeLieMkLinear_mem_lieHigh_of_magmaToFreeAlgebra_mem X
    change PBW.freeLieToFreeAlgebra ℤ X (freeLieMkLinear X p) ∈ associativeHigh X (n + 1) at hx
    rwa [freeLieToFreeAlgebra_mk] at hx
  · rintro ⟨p,hp,rfl⟩
    rw [freeLieToFreeAlgebra_mk]
    exact magmaToFreeAlgebra_mem_high X hp

/-- Every nilpotent quotient has a concrete injective truncated-coordinate map. -/
def quotientCoordinates (n : ℕ) :
    (FreeLieAlgebra ℤ X ⧸ lowerCentral ℤ (FreeLieAlgebra ℤ X) n) →ₗ[ℤ]
      (FreeMonoid X →₀ ℤ) :=
  (lowerCentral ℤ (FreeLieAlgebra ℤ X) n).toSubmodule.liftQ (coordinates X n)
    (fun x hx => (coordinates_eq_zero_iff X n x).mpr hx)

theorem quotientCoordinates_injective (n : ℕ) : Function.Injective (quotientCoordinates X n) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective
    (lowerCentral ℤ (FreeLieAlgebra ℤ X) n).toSubmodule x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((coordinates_eq_zero_iff X n x).mp hx)

/-- The manuscript's free-module input holds for arbitrary countable generator types. -/
theorem quotient_free [Countable X] (n : ℕ) :
    Module.Free ℤ (FreeLieAlgebra ℤ X ⧸ lowerCentral ℤ (FreeLieAlgebra ℤ X) n) :=
  Parafree.Linear.CountablePID.free_of_injective (Finsupp.basisSingleOne)
    (quotientCoordinates X n) (quotientCoordinates_injective X n)

end Parafree.Lie.FreeTruncation
