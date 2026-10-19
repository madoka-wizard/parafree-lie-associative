import Parafree.Associative.Quotient

/-! Augmented algebra maps and their actual finite augmentation quotients. -/
noncomputable section
namespace Parafree.Associative
variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]

abbrev augmentationIdeal (ε : A →ₐ[R] R) : Ideal A := RingHom.ker ε

def augmentationResidual (ε : A →ₐ[R] R) : Ideal A := ⨅ n : ℕ, augmentationIdeal ε ^ n

def ResiduallyNilpotent (ε : A →ₐ[R] R) : Prop := augmentationResidual ε = ⊥

structure AugmentedHom (ε : A →ₐ[R] R) (δ : B →ₐ[R] R) extends A →ₐ[R] B where
  augmentation : δ.comp toAlgHom = ε

namespace AugmentedHom
variable {ε : A →ₐ[R] R} {δ : B →ₐ[R] R} {η : C →ₐ[R] R}

@[simp] theorem augmentation_apply (f : AugmentedHom ε δ) (x : A) :
    δ (f.toAlgHom x) = ε x := AlgHom.congr_fun f.augmentation x

def id (ε : A →ₐ[R] R) : AugmentedHom ε ε where
  toAlgHom := AlgHom.id R A
  augmentation := rfl

def comp (g : AugmentedHom δ η) (f : AugmentedHom ε δ) : AugmentedHom ε η where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  augmentation := by ext x; exact (g.augmentation_apply _).trans (f.augmentation_apply x)

theorem mem_power (f : AugmentedHom ε δ) (n : ℕ) {x : A}
    (hx : x ∈ augmentationIdeal ε ^ n) : f.toAlgHom x ∈ augmentationIdeal δ ^ n :=
  map_mem_idealPower f.toAlgHom.toRingHom _ _
    (fun x hx => (f.augmentation_apply x).trans hx) n hx

def quotientMap (f : AugmentedHom ε δ) (n : ℕ) :
    A ⧸ augmentationIdeal ε ^ n →ₐ[R] B ⧸ augmentationIdeal δ ^ n :=
  quotientLift _ ((Ideal.Quotient.mkₐ R _).comp f.toAlgHom) (fun _ hx =>
    (Ideal.Quotient.eq_zero_iff_mem).mpr (f.mem_power n hx))

@[simp] theorem quotientMap_mk (f : AugmentedHom ε δ) (n : ℕ) (x : A) :
    f.quotientMap n (Ideal.Quotient.mkₐ R _ x) = Ideal.Quotient.mkₐ R _ (f.toAlgHom x) := rfl

def IsParaEquivalence (f : AugmentedHom ε δ) : Prop :=
  ∀ n : ℕ, Function.Bijective (f.quotientMap n)

theorem quotientMap_comp (g : AugmentedHom δ η) (f : AugmentedHom ε δ) (n : ℕ) :
    (g.comp f).quotientMap n = (g.quotientMap n).comp (f.quotientMap n) := by
  apply Ideal.Quotient.algHom_ext R
  rfl

theorem paraEquivalence_comp (g : AugmentedHom δ η) (f : AugmentedHom ε δ)
    (hg : g.IsParaEquivalence) (hf : f.IsParaEquivalence) : (g.comp f).IsParaEquivalence := by
  intro n
  rw [quotientMap_comp]
  exact (hg n).comp (hf n)

/-- Surjectivity also lifts every finite augmentation power. -/
theorem lift_mem_power (f : AugmentedHom ε δ) (hf : Function.Surjective f.toAlgHom)
    (n : ℕ) {y : B} (hy : y ∈ augmentationIdeal δ ^ n) :
    ∃ x ∈ augmentationIdeal ε ^ n, f.toAlgHom x = y := by
  induction n generalizing y with
  | zero =>
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨x, by rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial, rfl⟩
  | succ n ih =>
    rw [Submodule.pow_succ] at hy ⊢
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨x,hx,rfl⟩ := ih ha
      obtain ⟨z,rfl⟩ := hf b
      have hz : z ∈ augmentationIdeal ε := by
        change ε z = 0
        exact (f.augmentation_apply z).symm.trans hb
      exact ⟨x*z, Ideal.mul_mem_mul hx hz, map_mul _ _ _⟩
    · rintro a b ⟨x,hx,hx'⟩ ⟨y,hy,hy'⟩
      exact ⟨x+y, Submodule.add_mem _ hx hy, (map_add _ _ _).trans (congrArg₂ (· + ·) hx' hy')⟩

theorem quotientMap_bijective (f : AugmentedHom ε δ) (hf : Function.Surjective f.toAlgHom)
    (n : ℕ) (hker : RingHom.ker f.toAlgHom ≤ augmentationIdeal ε ^ n) :
    Function.Bijective (f.quotientMap n) := by
  constructor
  · intro x y hxy
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective R (augmentationIdeal ε ^ n) x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective R (augmentationIdeal ε ^ n) y
    have hab : f.toAlgHom (a-b) ∈ augmentationIdeal δ ^ n := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_sub]
      exact sub_eq_zero.mpr hxy
    obtain ⟨c,hc,he⟩ := f.lift_mem_power hf n hab
    have hd : a-b-c ∈ augmentationIdeal ε ^ n := hker (by
      change f.toAlgHom (a-b-c) = 0
      rw [map_sub, he, sub_self])
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [sub_add_cancel] using (augmentationIdeal ε ^ n).add_mem hd hc
  · intro y
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective R (augmentationIdeal δ ^ n) y
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨Ideal.Quotient.mkₐ R _ a,rfl⟩

theorem paraEquivalence_of_kernel_le_residual (f : AugmentedHom ε δ)
    (hf : Function.Surjective f.toAlgHom)
    (hker : RingHom.ker f.toAlgHom ≤ augmentationResidual ε) : f.IsParaEquivalence :=
  fun n => f.quotientMap_bijective hf n (hker.trans (iInf_le _ n))

theorem residual_eq_kernel (f : AugmentedHom ε δ)
    (hker : RingHom.ker f.toAlgHom ≤ augmentationResidual ε) (hδ : ResiduallyNilpotent δ) :
    augmentationResidual ε = RingHom.ker f.toAlgHom := by
  apply le_antisymm _ hker
  intro x hx
  have hy : f.toAlgHom x ∈ augmentationResidual δ := by
    change f.toAlgHom x ∈ ⨅ n : ℕ, augmentationIdeal δ ^ n
    simp only [Submodule.mem_iInf]
    intro n
    exact f.mem_power n ((Submodule.mem_iInf (fun n : ℕ => augmentationIdeal ε ^ n)).mp hx n)
  rw [hδ] at hy
  exact hy

theorem residuallyNilpotent_of_injective (f : AugmentedHom ε δ)
    (hf : Function.Injective f.toAlgHom) (hδ : ResiduallyNilpotent δ) : ResiduallyNilpotent ε := by
  apply le_antisymm _ bot_le
  intro x hx
  apply hf
  rw [map_zero]
  have hy : f.toAlgHom x ∈ augmentationResidual δ := by
    change f.toAlgHom x ∈ ⨅ n : ℕ, augmentationIdeal δ ^ n
    simp only [Submodule.mem_iInf]
    intro n
    exact f.mem_power n ((Submodule.mem_iInf (fun n : ℕ => augmentationIdeal ε ^ n)).mp hx n)
  rw [hδ] at hy
  exact hy

/-- The augmentation descends to positive finite augmentation quotients. -/
def quotientAugmentation (ε : A →ₐ[R] R) (n : ℕ) (hn : n ≠ 0) :
    A ⧸ augmentationIdeal ε ^ n →ₐ[R] R :=
  quotientLift _ ε (Ideal.pow_le_self hn)

def truncation (ε : A →ₐ[R] R) (n : ℕ) (hn : n ≠ 0) :
    AugmentedHom ε (quotientAugmentation ε n hn) where
  toAlgHom := Ideal.Quotient.mkₐ R _
  augmentation := rfl

@[simp] theorem quotientAugmentation_mk (ε : A →ₐ[R] R) (n : ℕ) (hn : n ≠ 0) (x : A) :
    quotientAugmentation ε n hn (Ideal.Quotient.mkₐ R _ x) = ε x := rfl

theorem quotientAugmentation_power_eq_bot (ε : A →ₐ[R] R) (n : ℕ) (hn : n ≠ 0) :
    augmentationIdeal (quotientAugmentation ε n hn) ^ n = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨a,ha,rfl⟩ := (truncation ε n hn).lift_mem_power
    (Ideal.Quotient.mkₐ_surjective R _) n hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

def liftNilpotent (f : AugmentedHom ε δ) (n : ℕ)
    (hn : augmentationIdeal δ ^ n = ⊥) : A ⧸ augmentationIdeal ε ^ n →ₐ[R] B :=
  quotientLift _ f.toAlgHom (by
    intro x hx
    have h := f.mem_power n hx
    rw [hn] at h
    exact h)

end AugmentedHom
end Parafree.Associative
