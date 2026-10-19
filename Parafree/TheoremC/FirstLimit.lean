import Parafree.TheoremC.Presentation

/-! All higher relations vanish in every finite augmentation quotient of A₀.
This constructs the difficult inclusion into the first limit directly,
without using a completion or assuming separatedness of the full quotient. -/
noncomputable section
namespace Parafree.TheoremC
open Parafree.Associative
variable (k : Type*) [CommRing k]

abbrev initialAugmentationIdeal := augmentationIdeal (augmentation₀ k)
abbrev fullAugmentationIdeal := augmentationIdeal (augmentation k)
def truncate₀ (n : ℕ) : A₀ k →ₐ[k] A₀ k ⧸ initialAugmentationIdeal k ^ n :=
  Ideal.Quotient.mkₐ k _

theorem truncated_generator_nilpotent (n : ℕ) (i : Fin 6) :
    IsNilpotent (truncate₀ k n (generator₀ k i)) := by
  refine ⟨n, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.pow_mem_pow (augmentation₀_generator k i) n)

theorem higher_relator_truncated (n l : ℕ) :
    truncate₀ k n (toInitial k (relator k l)) = 0 := by
  let f := (truncate₀ k n).comp (toInitial k)
  have h₀ := congrArg (truncate₀ k n) (initial_relator k (0 : Fin 2))
  have h₁ := congrArg (truncate₀ k n) (initial_relator k (1 : Fin 2))
  have he₀ : (1 + f (letter k 0)) * (1 + f (letter k 2)) =
      (1 + f (letter k 3)) * (1 + f (letter k 5)) := by
    apply sub_eq_zero.mp
    simpa [relator, f, map_sub, map_mul, map_add, map_pow] using h₀
  have he₁ : (1 + f (letter k 0)) * (1 + f (letter k 1)) * (1 + f (letter k 2)) =
      (1 + f (letter k 3)) * (1 + f (letter k 4)) * (1 + f (letter k 5)) := by
    apply sub_eq_zero.mp
    simpa [relator, f, map_sub, map_mul, map_add, map_pow] using h₁
  have he := relations_of_nilpotent (f (letter k 0)) (f (letter k 1)) (f (letter k 2))
    (f (letter k 3)) (f (letter k 4)) (f (letter k 5))
    (truncated_generator_nilpotent k n 0) (truncated_generator_nilpotent k n 3)
    (truncated_generator_nilpotent k n 5) he₀ he₁ l
  change f (relator k l) = 0
  simpa only [relator, map_sub, map_mul, map_add, map_one, map_pow] using sub_eq_zero.mpr he

theorem fullIdeal_le_truncated_kernel (n : ℕ) :
    fullIdeal k ≤ RingHom.ker ((truncate₀ k n).comp (toInitial k)) :=
  twoSidedSpan_le (by rintro _ ⟨l,rfl⟩; exact higher_relator_truncated k n l)

theorem kernel_le_finitePower (n : ℕ) : kernel k ≤ initialAugmentationIdeal k ^ n := by
  intro x hx
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective k (initialIdeal k) x
  have ha : a ∈ fullIdeal k := Ideal.Quotient.eq_zero_iff_mem.mp hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp (fullIdeal_le_truncated_kernel k n ha)

theorem kernel_le_residual : kernel k ≤ augmentationResidual (augmentation₀ k) :=
  le_iInf (kernel_le_finitePower k)

/-- The second canonical map in Theorem D is already a para-equivalence,
independently of the normal-form and homology calculations. -/
theorem projection_isParaEquivalence : (augmentedProjection k).IsParaEquivalence :=
  (augmentedProjection k).paraEquivalence_of_kernel_le_residual
    (projection_surjective k) (kernel_le_residual k)

theorem firstLimit_eq_kernel_of_separated
    (h : ResiduallyNilpotent (augmentation k)) :
    augmentationResidual (augmentation₀ k) = kernel k :=
  (augmentedProjection k).residual_eq_kernel (kernel_le_residual k) h

end Parafree.TheoremC
