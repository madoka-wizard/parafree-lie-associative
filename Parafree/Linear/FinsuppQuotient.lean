import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Isomorphisms

/-! Quotients commute with arbitrary finitely supported families. -/

noncomputable section

namespace Parafree.Linear.FinsuppQuotient

variable (X : Type*) {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (P : Submodule R M)

def map : (X →₀ M) →ₗ[R] (X →₀ (M ⧸ P)) := Finsupp.mapRange.linearMap P.mkQ

theorem surjective : Function.Surjective (map X P) :=
  Finsupp.mapRange_surjective P.mkQ P.mkQ.map_zero P.mkQ_surjective

theorem ker : (map X P).ker = Finsupp.submodule (fun _ : X => P) := by
  rw [map, Finsupp.ker_mapRange, Submodule.ker_mkQ]

def equiv : ((X →₀ M) ⧸ Finsupp.submodule (fun _ : X => P)) ≃ₗ[R] (X →₀ (M ⧸ P)) :=
  (Submodule.quotEquivOfEq _ _ (ker X P).symm).trans
    ((map X P).quotKerEquivOfSurjective (surjective X P))

end Parafree.Linear.FinsuppQuotient
