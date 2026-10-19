import Parafree.Lie.LowerCentral
import LieRings.DimensionSubring.Centrality

/-! The lower central powers of an ideal, retained as ideals of the ambient algebra. -/

namespace Parafree.Lie

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

-- The explicit instances avoid the competing subtype discrimination keys of
-- Lie ideals and Lie submodules. They are the existing ambient adjoint action.
local instance (I : LieIdeal R L) : LieRingModule L I :=
  LieSubmodule.instLieRingModuleSubtypeMem I
local instance (I : LieIdeal R L) : LieModule R L I :=
  LieSubmodule.instLieModule I

/-- The intrinsic lower central series of an ideal, embedded as ambient ideals. -/
def idealLowerCentral (I : LieIdeal R L) (n : ℕ) : LieIdeal R L :=
  (I.lcs (I : LieSubmodule R L L) n).map (LieSubmodule.incl I)

theorem idealLowerCentral_toSubmodule (I : LieIdeal R L) (n : ℕ) :
    (idealLowerCentral I n).toSubmodule =
      (lowerCentral R I n).toSubmodule.map I.toSubmodule.subtype := by
  change (I.lcs (I : LieSubmodule R L L) n).toSubmodule.map I.toSubmodule.subtype = _
  rw [LieIdeal.coe_lcs_eq]
  rfl

@[simp] theorem mem_idealLowerCentral (I : LieIdeal R L) (n : ℕ) (x : L) :
    x ∈ idealLowerCentral I n ↔
      ∃ hx : x ∈ I, (⟨x, hx⟩ : I) ∈ lowerCentral R I n := by
  change x ∈ (idealLowerCentral I n).toSubmodule ↔ _
  rw [idealLowerCentral_toSubmodule]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨x, hx⟩, hy, rfl⟩

/-- The conventional positive degrees add under the bracket. -/
theorem bracket_lowerCentral_le (m n : ℕ) :
    ⁅lowerCentral R L m, lowerCentral R L n⁆ ≤ lowerCentral R L (m + n + 1) :=
  (LieSubmodule.mono_lie
    (LieRings.lowerCentralSeries_le_dimensionSubring R L m)
    (LieRings.lowerCentralSeries_le_dimensionSubring R L n)).trans
    (LieRings.bracket_dimensionSubring_le_lowerCentralSeries R L m n)

theorem bracket_idealLowerCentral_le (I : LieIdeal R L) (m n : ℕ) :
    ⁅idealLowerCentral I m, idealLowerCentral I n⁆ ≤ idealLowerCentral I (m + n + 1) := by
  rw [LieSubmodule.lie_le_iff]
  intro x hx y hy
  obtain ⟨hxI, hx⟩ := (mem_idealLowerCentral I m x).mp hx
  obtain ⟨hyI, hy⟩ := (mem_idealLowerCentral I n y).mp hy
  have hb := (bracket_lowerCentral_le (R := R) (L := I) m n)
    (LieSubmodule.lie_mem_lie hx hy)
  exact (mem_idealLowerCentral I (m + n + 1) ⁅x, y⁆).mpr
    ⟨I.lie_mem hyI, hb⟩

/-- The ambient algebra in degree zero and the positive ideal powers thereafter. -/
def idealPowerFiltration (I : LieIdeal R L) : ℕ → LieIdeal R L
  | 0 => ⊤
  | n + 1 => idealLowerCentral I n

theorem idealPowerFiltration_bracket (I : LieIdeal R L) (m n : ℕ) :
    ⁅idealPowerFiltration I m, idealPowerFiltration I n⁆ ≤
      idealPowerFiltration I (m + n) := by
  cases m with
  | zero =>
    simpa only [Nat.zero_add, idealPowerFiltration] using
      LieSubmodule.lie_le_right (idealPowerFiltration I n) (⊤ : LieIdeal R L)
  | succ m =>
    cases n with
    | zero =>
      rw [Nat.add_zero]
      exact LieSubmodule.lie_le_left _ _
    | succ n =>
      change ⁅idealLowerCentral I m, idealLowerCentral I n⁆ ≤ _
      have he : m + 1 + (n + 1) = (m + n + 1) + 1 := by omega
      rw [he]
      exact bracket_idealLowerCentral_le I m n

end Parafree.Lie
