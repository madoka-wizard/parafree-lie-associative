import Parafree.Homology.ExteriorNaturality

noncomputable section

namespace Parafree.Homology.ExteriorScalarChange

open LieRings.Homological.LieHomology
open Parafree.Linear.ExteriorBaseChange
open scoped TensorProduct Parafree.Linear.ExteriorBaseChange

variable {R : Type*} [CommRing R] {L : Type*} [LieRing L] [LieAlgebra R L]

variable (S : Type*) [CommRing S] [Algebra R S]

def tensorUnit : L →ₗ⁅R⁆ S ⊗[R] L where
  __ := TensorProduct.mk R S L 1
  map_lie' {x y} := by
    change (1 : S) ⊗ₜ[R] ⁅x, y⁆ = ⁅(1 : S) ⊗ₜ[R] x, (1 : S) ⊗ₜ[R] y⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]

@[simp] theorem inclusion_one (x : L) :
    inclusion S 1 (exteriorPower.ιMulti R 1 ![x]) =
      exteriorPower.ιMulti S 1 ![(1 : S) ⊗ₜ[R] x] := by
  rw [inclusion_wedge]
  congr 1
  funext i
  fin_cases i
  rfl

@[simp] theorem inclusion_two (x y : L) :
    inclusion S 2 (exteriorPower.ιMulti R 2 ![x, y]) =
      exteriorPower.ιMulti S 2 ![(1 : S) ⊗ₜ[R] x, (1 : S) ⊗ₜ[R] y] := by
  rw [inclusion_wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem inclusion_three (x y z : L) :
    inclusion S 3 (exteriorPower.ιMulti R 3 ![x, y, z]) =
      exteriorPower.ιMulti S 3 ![(1 : S) ⊗ₜ[R] x, (1 : S) ⊗ₜ[R] y,
        (1 : S) ⊗ₜ[R] z] := by
  rw [inclusion_wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem inclusion_differential_one (x : ⋀[R]^2 L) :
    inclusion S 1 (differential R L 1 x) =
      differential S (S ⊗[R] L) 1 (inclusion S 2 x) := by
  exact along_differential_one S (tensorUnit S) x

theorem inclusion_differential_two (x : ⋀[R]^3 L) :
    inclusion S 2 (differential R L 2 x) =
      differential S (S ⊗[R] L) 2 (inclusion S 3 x) := by
  exact along_differential_two S (tensorUnit S) x

end Parafree.Homology.ExteriorScalarChange
