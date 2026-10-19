import Parafree.Lie.LowerCentral
import LieRings.DimensionSubring.FreeLie

/-! Residual nilpotence of integral free Lie algebras from the verified word filtration. -/

namespace Parafree.Lie

open LieRings LieRings.FreeLieDimension

variable (X : Type*)

theorem freeLie_residuallyNilpotent : ResiduallyNilpotent ℤ (FreeLieAlgebra ℤ X) := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply freeLieToFreeAlgebra_injective_int X
  rw [map_zero]
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  rw [map_zero]
  ext w
  by_contra hw
  have hmem : w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (PBW.freeLieToFreeAlgebra ℤ X x)).support := Finsupp.mem_support_iff.mpr hw
  have hxhigh := lowerCentralSeries_le_lieHigh X w.length ((residualIdeal_le w.length) hx)
  obtain ⟨p, hp, hpmap⟩ := hxhigh
  have heval : PBW.freeLieToFreeAlgebra ℤ X x ∈ associativeHigh X (w.length + 1) := by
    rw [← hpmap, freeLieToFreeAlgebra_mk]
    exact magmaToFreeAlgebra_mem_high X hp
  have hlen : w.length + 1 ≤ w.length := heval hmem
  omega

theorem residuallyNilpotent_of_injective {L M : Type*} [LieRing L] [LieRing M]
    (f : L →ₗ⁅ℤ⁆ M) (hf : Function.Injective f) (hM : ResiduallyNilpotent ℤ M) :
    ResiduallyNilpotent ℤ L := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply hf
  rw [map_zero]
  have hm : f x ∈ residualIdeal ℤ M := by
    rw [residualIdeal, LieSubmodule.mem_iInf]
    intro n
    exact map_mem_lowerCentral f n ((residualIdeal_le n) hx)
  simpa only [show residualIdeal ℤ M = ⊥ from hM, LieSubmodule.mem_bot] using hm

end Parafree.Lie
