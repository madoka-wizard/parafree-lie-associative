import Parafree.Homology.Coefficients.RegularAcyclicity
import Parafree.Homology.Coefficients.DirectSum

/-!
# Direct sums of regular enveloping coefficients

The input needed here is an equivariant equivalence with a direct sum of regular
modules. Freeness of the underlying base-ring module alone does not suffice.
All vanishing statements concern the actual coefficient CE complex.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.Enveloping

open scoped DirectSum
open Parafree.Linear.ExteriorTensor (Chain)

universe u w z
variable (R L : Type u) [CommRing R] [LieRing L] [LieAlgebra R L] [Module.Free R L]
variable (ι : Type z) [DecidableEq ι]

theorem directSum_fill (n : ℕ) (x : Chain R L (⨁ _ : ι, Regular R L) (n + 1))
    (hx : differential R L (⨁ _ : ι, Regular R L) n x = 0) :
    ∃ y, differential R L (⨁ _ : ι, Regular R L) (n + 1) y = x :=
  DirectSums.fill R L (fun _ : ι => Regular R L) n (fun _ => fill R L n) x hx

theorem directSum_exactAt (n : ℕ) (hn : n ≠ 0) :
    (complex R L (⨁ _ : ι, Regular R L)).ExactAt n :=
  DirectSums.exactAt R L (fun _ : ι => Regular R L) n hn (fun _ => exactAt R L n hn)

theorem directSum_homology_isZero (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (homology R L (⨁ _ : ι, Regular R L) n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (directSum_exactAt R L ι n hn)

variable {R L ι}
variable {M : Type w} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem exactAt_of_regular_equiv (e : M ≃ₗ⁅R,L⁆ (⨁ _ : ι, Regular R L))
    (n : ℕ) (hn : n ≠ 0) : (complex R L M).ExactAt n :=
  exactAt_of_equiv e n hn (directSum_exactAt R L ι n hn)

theorem homology_isZero_of_regular_equiv (e : M ≃ₗ⁅R,L⁆ (⨁ _ : ι, Regular R L))
    (n : ℕ) (hn : n ≠ 0) : CategoryTheory.Limits.IsZero (homology R L M n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp
    (exactAt_of_regular_equiv e n hn)

section DimensionShift

variable {W P : Type u}
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]
  [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

/-- A proved equivariant presentation of the augmentation ideal gives two shifts.
The exact coefficient sequence is an input; all required vanishing results are
supplied here from an equivariant regular-module decomposition of its middle term. -/
def dimensionShiftAugmentation
    {f : W →ₗ⁅R,L⁆ P} {g : P →ₗ⁅R,L⁆ ideal R L} {hfg : g.comp f = 0}
    (h : (sequence f g hfg).ShortExact) (e : P ≃ₗ⁅R,L⁆ (⨁ _ : ι, Regular R L))
    (n : ℕ) (hn : n ≠ 0) :
    Homology R L W n ≃ₗ[R]
      LieRings.Homological.LieHomology.Homology (R := R) (L := L) (n + 2) :=
  (dimensionShift h n
    (homology_isZero_of_regular_equiv e (n + 1) (by omega))
    (homology_isZero_of_regular_equiv e n hn)).symm.trans
      (augmentationHomologyEquiv R L n)

end DimensionShift

end Parafree.Homology.Coefficients.Enveloping
