import Parafree.TheoremC.InitialHom
import Parafree.TheoremC.FirstLimit

/-! Explicit inverse on each positive finite augmentation quotient.
The construction is uniform over commutative coefficient rings. -/
noncomputable section
namespace Parafree.TheoremC.NilpotentInverse
open Parafree.Associative
variable (k : Type*) [CommRing k] (n : ℕ)

abbrev F := FreeAlgebra k (Fin 4)
abbrev Q := F k ⧸ augmentationIdeal (fourAugmentation k) ^ (n+1)
def q : F k →ₐ[k] Q k n := Ideal.Quotient.mkₐ k _
def ε : Q k n →ₐ[k] k := AugmentedHom.quotientAugmentation (fourAugmentation k) (n+1) (by omega)
def t (i : Fin 4) : Q k n := q k n (FreeAlgebra.ι k i)

@[simp] theorem ε_t (i : Fin 4) : ε k n (t k n i) = 0 := FreeAlgebra.lift_ι_apply _ _

theorem t_nilpotent (i : Fin 4) : IsNilpotent (t k n i) := by
  refine ⟨n+1, ?_⟩
  rw [t, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow (FreeAlgebra.lift_ι_apply _ i) (n+1))

def unit (i : Fin 4) : (Q k n)ˣ := (t_nilpotent k n i).isUnit_one_add.unit
@[simp] theorem unit_coe (i : Fin 4) : (unit k n i : Q k n) = 1 + t k n i :=
  (t_nilpotent k n i).isUnit_one_add.unit_spec

@[simp] theorem ε_unit (i : Fin 4) : ε k n (unit k n i) = 1 := by simp
@[simp] theorem ε_unit_inv (i : Fin 4) : ε k n (↑((unit k n i)⁻¹) : Q k n) = 1 := by
  have h := congrArg (ε k n) (Units.mul_inv (unit k n i))
  simpa using h

def values : Fin 6 → Q k n := ![t k n 0, t k n 1, t k n 2, t k n 3,
  solvedX (unit k n 0) (unit k n 3) (1+t k n 1) - 1,
  solvedY (unit k n 0) (unit k n 3) (1+t k n 2) - 1]

@[simp] theorem ε_values (i : Fin 6) : ε k n (values k n i) = 0 := by
  fin_cases i <;> simp [values, solvedX, solvedY]

def evaluate : Free k →ₐ[k] Q k n := FreeAlgebra.lift k (values k n)
@[simp] theorem evaluate_letter (i : Fin 6) : evaluate k n (letter k i) = values k n i :=
  FreeAlgebra.lift_ι_apply _ _

theorem evaluate_initial_relator (i : Fin 2) : evaluate k n (relator k i) = 0 := by
  fin_cases i
  · have h := solved_zero (unit k n 0) (unit k n 3) (1+t k n 2)
    simpa [relator, values, ← add_sub_assoc] using sub_eq_zero.mpr h
  · have h := solved_one (unit k n 0) (unit k n 3) (1+t k n 1) (1+t k n 2)
    simpa [relator, values, ← add_sub_assoc] using sub_eq_zero.mpr h

def fromInitial : A₀ k →ₐ[k] Q k n := quotientLift _ (evaluate k n)
  (twoSidedSpan_le (by rintro _ ⟨i,rfl⟩; exact evaluate_initial_relator k n i))

@[simp] theorem fromInitial_generator (i : Fin 6) : fromInitial k n (generator₀ k i) = values k n i :=
  evaluate_letter k n i

def augmentedFromInitial : AugmentedHom (augmentation₀ k) (ε k n) where
  toAlgHom := fromInitial k n
  augmentation := by
    apply initialHom_ext
    intro i
    change ε k n (fromInitial k n (generator₀ k i)) = augmentation₀ k (generator₀ k i)
    simp

def inverse : A₀ k ⧸ initialAugmentationIdeal k ^ (n+1) →ₐ[k] Q k n :=
  (augmentedFromInitial k n).liftNilpotent (n+1)
    (AugmentedHom.quotientAugmentation_power_eq_bot (fourAugmentation k) (n+1) (by omega))

def forward : Q k n →ₐ[k] A₀ k ⧸ initialAugmentationIdeal k ^ (n+1) :=
  (augmentedFourToInitial k).quotientMap (n+1)

@[simp] theorem inverse_mk (x : A₀ k) : inverse k n (truncate₀ k (n+1) x) = fromInitial k n x := rfl

@[simp] theorem forward_t (i : Fin 4) : forward k n (t k n i) =
    truncate₀ k (n+1) (generator₀ k i.castSucc.castSucc) := by
  change Ideal.Quotient.mkₐ k _ (fourToInitial k (FreeAlgebra.ι k i)) = _
  rw [fourToInitial, FreeAlgebra.lift_ι_apply]
  rfl

theorem inverse_forward : (inverse k n).comp (forward k n) = AlgHom.id k (Q k n) := by
  apply Ideal.Quotient.algHom_ext k
  apply FreeAlgebra.hom_ext
  funext i
  change inverse k n (forward k n (t k n i)) = t k n i
  rw [forward_t, inverse_mk, fromInitial_generator]
  fin_cases i <;> rfl

theorem forward_inverse : (forward k n).comp (inverse k n) = AlgHom.id k _ := by
  apply Ideal.Quotient.algHom_ext k
  apply initialHom_ext_four
  · intro i
    change forward k n (fromInitial k n (generator₀ k i.castSucc.castSucc)) =
      truncate₀ k (n+1) (generator₀ k i.castSucc.castSucc)
    rw [fromInitial_generator]
    fin_cases i <;> exact forward_t k n _
  · exact (truncated_generator_nilpotent k (n+1) 0).isUnit_one_add
  · exact (truncated_generator_nilpotent k (n+1) 2).isUnit_one_add
  · exact (truncated_generator_nilpotent k (n+1) 3).isUnit_one_add

theorem forward_bijective : Function.Bijective (forward k n) := by
  constructor
  · exact Function.LeftInverse.injective (fun x => AlgHom.congr_fun (inverse_forward k n) x)
  · exact Function.RightInverse.surjective (fun x => AlgHom.congr_fun (forward_inverse k n) x)

end Parafree.TheoremC.NilpotentInverse
