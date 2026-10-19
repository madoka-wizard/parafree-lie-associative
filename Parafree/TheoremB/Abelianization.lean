import Parafree.TheoremB.Parafree
import Parafree.Lie.FreeAbelianization
import LieRings.Homological.LieHomology.LowDegreeHomology

/-! The abelianization and actual first CE homology are free of rank two. -/

noncomputable section
namespace Parafree.TheoremB

open Parafree.Lie
open LieRings.Homological.LieHomology

def abelianizationEquiv : Abelianization ≃ₗ⁅ℤ⁆ (Fin 2 → ℤ) :=
  (LieEquiv.ofBijective (nilpotentMap freeToP 1) (freeToP_isParaEquivalence 1)).symm.trans
    (FreeAbelianization.equiv 2)

instance abelianization_isTorsionFree : Module.IsTorsionFree ℤ Abelianization :=
  Function.Injective.moduleIsTorsionFree (R := ℤ)
    abelianizationEquiv abelianizationEquiv.injective
    (fun r z => abelianizationEquiv.toLinearEquiv.map_smul r z)

def homologyOneEquiv : Homology (R := ℤ) (L := P) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (homologyOneEquivAbelianization ℤ P).trans (by
    simpa only [lowerCentral, LieModule.lowerCentralSeries_succ,
      LieModule.lowerCentralSeries_zero] using abelianizationEquiv.toLinearEquiv)

end Parafree.TheoremB
