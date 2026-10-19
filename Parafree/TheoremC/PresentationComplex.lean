import Parafree.TheoremC.RightIndependent

/-! The presentation complex for the actual infinitely presented algebra A. -/
noncomputable section
namespace Parafree.TheoremC.PresentationComplex
open Parafree.Associative
variable (k : Type*) [CommRing k]

abbrev P₁ := Fin 6 →₀ A k
abbrev P₂ := ℕ →₀ A k

def coefficients : (Fin 6 →₀ Free k) →ₗ[k] P₁ k :=
  Finsupp.mapRange.linearMap (toFull k).toLinearMap

@[simp] theorem coefficients_single (i : Fin 6) (a : Free k) :
    coefficients k (Finsupp.single i a) = Finsupp.single i (toFull k a) := by
  simp [coefficients]

theorem coefficients_smul (a : Free k) (v : Fin 6 →₀ Free k) :
    coefficients k (a • v) = toFull k a • coefficients k v := by
  ext i
  change toFull k (a * v i) = toFull k a * toFull k (v i)
  exact map_mul _ _ _

theorem coefficients_surjective : Function.Surjective (coefficients k) := by
  intro v
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0,map_zero _⟩
  | add v w hv hw =>
    obtain ⟨a,rfl⟩ := hv
    obtain ⟨b,rfl⟩ := hw
    exact ⟨a+b,map_add _ _ _⟩
  | single i a =>
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective k (fullIdeal k) a
    exact ⟨Finsupp.single i b,coefficients_single k i b⟩

def d₁ : P₁ k →ₗ[A k] A k := Finsupp.linearCombination (A k) (generator k)
def D : Free k →ₗ[k] P₁ k :=
  (coefficients k).comp (FreeAugmentation.derivative k (Fin 6))
def d₂ : P₂ k →ₗ[A k] P₁ k :=
  Finsupp.linearCombination (A k) (fun i : ℕ => D k (relator k i))

theorem d₁_coefficients (v : Fin 6 →₀ Free k) :
    d₁ k (coefficients k v) = toFull k (FreeAugmentation.concatenate k (Fin 6) v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single i a => simp [d₁, generator, letter, FreeAugmentation.concatenate_single]

theorem d₁_D (a : Free k) : d₁ k (D k a) =
    toFull k a - algebraMap k (A k) (freeAugmentation k a) := by
  rw [D, LinearMap.comp_apply, d₁_coefficients, FreeAugmentation.concatenate_derivative]
  simp only [map_sub, AlgHom.commutes]
  rfl

theorem D_mul (a b : Free k) : D k (a*b) =
    toFull k a • D k b + freeAugmentation k b • D k a := by
  change coefficients k (FreeAugmentation.derivative k (Fin 6) (a*b)) = _
  rw [FreeAugmentation.derivative_mul, map_add, coefficients_smul, map_smul]
  rfl

theorem d₁_d₂ : (d₁ k).comp (d₂ k) = 0 := by
  apply Finsupp.lhom_ext
  intro i a
  simp [d₂, d₁_D]

theorem D_mem_range {a : Free k} (ha : a ∈ fullIdeal k) :
    D k a ∈ LinearMap.range (d₂ k) := by
  induction ha using TwoSidedIdeal.span_induction with
  | mem a ha =>
    obtain ⟨i,rfl⟩ := ha
    exact ⟨Finsupp.single i 1, by simp [d₂]⟩
  | zero => simp
  | add a b _ _ ha hb => simpa using (LinearMap.range (d₂ k)).add_mem ha hb
  | neg a _ ha => simpa using (LinearMap.range (d₂ k)).neg_mem ha
  | left_absorb a b hb ih =>
    have he : freeAugmentation k b = 0 :=
      (fullIdeal_le_augmentation k) hb
    rw [D_mul, he, zero_smul, add_zero]
    exact (LinearMap.range (d₂ k)).smul_mem _ ih
  | right_absorb b a ha ih =>
    have he : toFull k a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [D_mul, he, zero_smul, zero_add]
    exact ((LinearMap.range (d₂ k)).restrictScalars k).smul_mem _ ih

theorem exact_d₂_d₁ : Function.Exact (d₂ k) (d₁ k) := by
  intro v
  constructor
  · intro hv
    obtain ⟨w,rfl⟩ := coefficients_surjective k v
    have hw : FreeAugmentation.concatenate k (Fin 6) w ∈ fullIdeal k :=
      Ideal.Quotient.eq_zero_iff_mem.mp ((d₁_coefficients k w).symm.trans hv)
    have he := D_mem_range k hw
    simpa only [D, LinearMap.comp_apply, FreeAugmentation.derivative_concatenate] using he
  · rintro ⟨v,rfl⟩
    exact LinearMap.congr_fun (d₁_d₂ k) v

def q : A k →ₗ[A k] (A k ⧸ augmentationIdeal (augmentation k)) :=
  (augmentationIdeal (augmentation k)).mkQ

theorem exact_d₁_q : Function.Exact (d₁ k) (q k) := by
  intro a
  constructor
  · intro ha
    have hz : augmentation k a = 0 := (Submodule.Quotient.mk_eq_zero _).mp ha
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective k (fullIdeal k) a
    refine ⟨D k b, ?_⟩
    change freeAugmentation k b = 0 at hz
    rw [d₁_D, hz, map_zero, sub_zero]
    rfl
  · rintro ⟨v,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change augmentation k (d₁ k v) = 0
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp [hv, hw]
    | single i a => simp [d₁, smul_eq_mul]

@[simp] theorem D_one : D k 1 = 0 := by simp [D]

@[simp] theorem D_letter (i : Fin 6) : D k (letter k i) = Finsupp.single i 1 := by
  have he : FreeAugmentation.derivative k (Fin 6) (letter k i) = Finsupp.single i 1 := by
    simpa [letter] using FreeAugmentation.derivative_concatenate_single k (Fin 6) i 1
  simp [D, he]

theorem D_pow_shifted_third (n : ℕ) : D k ((1+letter k 1)^n) 2 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, D_mul, ih]

theorem D_pow_other_third (n : ℕ) : D k ((1+letter k 4)^n) 2 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, D_mul, ih]

theorem D_relator_third (n : ℕ) :
    D k (relator k n) 2 = (1+generator k 0) * (1+generator k 1)^n := by
  simp [relator, D_mul, D_pow_shifted_third, D_pow_other_third, generator]

theorem d₂_third (v : P₂ k) : d₂ k v 2 = RightIndependent.multiply k v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, Finsupp.add_apply, hv, hw]
  | single n a => simp [d₂, RightIndependent.multiply, D_relator_third, smul_eq_mul]

/-- The infinite presentation has no relations among its left-module relators. -/
theorem d₂_injective : Function.Injective (d₂ k) := by
  intro v w h
  apply RightIndependent.multiply_injective k
  simpa only [d₂_third] using congrArg (fun x : P₁ k => x 2) h

end Parafree.TheoremC.PresentationComplex
