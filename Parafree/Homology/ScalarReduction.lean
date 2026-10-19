import Parafree.Linear.ModScalar
import Mathlib.Tactic.Abel

/-!
The degreewise reduction of a three-term complex commutes with middle homology
when multiplication by the scalar is injective in the last module and the last
differential has saturated image. No freeness hypothesis is needed here.
-/

noncomputable section

namespace Parafree.Homology.ScalarReduction

open Parafree.Linear

variable {R : Type*} [CommRing R]
variable {C₁ C₂ C₃ : Type*}
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
  [AddCommGroup C₃] [Module R C₃]

variable (d₂ : C₂ →ₗ[R] C₁) (d₃ : C₃ →ₗ[R] C₂) (h : d₂.comp d₃ = 0)

def boundary : C₃ →ₗ[R] d₂.ker := d₃.codRestrict _ (fun x => LinearMap.congr_fun h x)

abbrev Homology := d₂.ker ⧸ (boundary d₂ d₃ h).range

def homologyClass : d₂.ker →ₗ[R] Homology d₂ d₃ h := (boundary d₂ d₃ h).range.mkQ

theorem class_eq_zero (z : d₂.ker) :
    homologyClass d₂ d₃ h z = 0 ↔ ∃ b : C₃, d₃ b = z.val := by
  rw [homologyClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, Subtype.ext hb⟩

variable (r : R)

include h in
theorem reduced_comp : (ModScalar.map r d₂).comp (ModScalar.map r d₃) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := ModScalar.mk_surjective r C₃ x
  change ModScalar.map r d₂ (ModScalar.map r d₃ (ModScalar.mk r C₃ x)) = 0
  simp only [ModScalar.map_mk]
  rw [show d₂ (d₃ x) = 0 from LinearMap.congr_fun h x, map_zero]

abbrev ReducedHomology :=
  Homology (ModScalar.map r d₂) (ModScalar.map r d₃) (reduced_comp d₂ d₃ h r)

def reduceCycles : d₂.ker →ₗ[R] (ModScalar.map r d₂).ker :=
  ((ModScalar.mk r C₂).comp d₂.ker.subtype).codRestrict _ (fun z => by
    change ModScalar.map r d₂ (ModScalar.mk r C₂ z.val) = 0
    rw [ModScalar.map_mk, z.property, map_zero])

def reduceClass : d₂.ker →ₗ[R] ReducedHomology d₂ d₃ h r :=
  (homologyClass _ _ _).comp (reduceCycles d₂ r)

theorem reduce_boundary (b : C₃) :
    reduceClass d₂ d₃ h r (boundary d₂ d₃ h b) = 0 := by
  apply (class_eq_zero _ _ _ _).mpr
  exact ⟨ModScalar.mk r C₃ b, rfl⟩

def reduce : Homology d₂ d₃ h →ₗ[R] ReducedHomology d₂ d₃ h r :=
  (boundary d₂ d₃ h).range.liftQ (reduceClass d₂ d₃ h r) (by
    rintro _ ⟨b, rfl⟩
    exact reduce_boundary d₂ d₃ h r b)

@[simp] theorem reduce_class (z : d₂.ker) :
    reduce d₂ d₃ h r (homologyClass d₂ d₃ h z) = reduceClass d₂ d₃ h r z := rfl

theorem reduce_surjective
    (hsat : ∀ y : C₁, r • y ∈ d₂.range → y ∈ d₂.range) :
    Function.Surjective (reduce d₂ d₃ h r) := by
  intro q
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (boundary _ _ _).range q
  obtain ⟨x, hx⟩ := ModScalar.mk_surjective r C₂ z.val
  have hdx : ModScalar.mk r C₁ (d₂ x) = 0 := by
    rw [← ModScalar.map_mk, hx]
    exact z.property
  obtain ⟨y, hy⟩ := (ModScalar.mk_eq_zero r C₁ (d₂ x)).mp hdx
  obtain ⟨t, ht⟩ := hsat y ⟨x, hy.symm⟩
  let c : d₂.ker := ⟨x - r • t, by
    change d₂ (x - r • t) = 0
    rw [map_sub, map_smul, ht, hy, sub_self]⟩
  refine ⟨homologyClass d₂ d₃ h c, ?_⟩
  change homologyClass _ _ _ (reduceCycles d₂ r c) = homologyClass _ _ _ z
  congr 1
  apply Subtype.ext
  change ModScalar.mk r C₂ (x - r • t) = z.val
  rw [map_sub, ModScalar.mk_smul_self, sub_zero, hx]

theorem reduce_eq_zero_iff
    (hinj : Function.Injective (fun x : C₁ => r • x))
    (q : Homology d₂ d₃ h) :
    reduce d₂ d₃ h r q = 0 ↔ ∃ a : Homology d₂ d₃ h, r • a = q := by
  constructor
  · obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (boundary d₂ d₃ h).range q
    intro hz
    obtain ⟨bbar, hbbar⟩ := (class_eq_zero _ _ _ _).mp hz
    obtain ⟨b, rfl⟩ := ModScalar.mk_surjective r C₃ bbar
    have he : ModScalar.mk r C₂ (z.val - d₃ b) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hbbar.symm
    obtain ⟨a, ha⟩ := (ModScalar.mk_eq_zero r C₂ _).mp he
    have hda : d₂ a = 0 := by
      apply hinj
      change r • d₂ a = r • (0 : C₁)
      rw [smul_zero, ← map_smul, ha, map_sub, z.property,
        show d₂ (d₃ b) = 0 from LinearMap.congr_fun h b, sub_self]
    let ac : d₂.ker := ⟨a, hda⟩
    refine ⟨homologyClass d₂ d₃ h ac, ?_⟩
    change r • homologyClass d₂ d₃ h ac = homologyClass d₂ d₃ h z
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    apply (class_eq_zero d₂ d₃ h _).mpr
    refine ⟨-b, ?_⟩
    change d₃ (-b) = r • a - z.val
    rw [map_neg, ha]
    abel
  · rintro ⟨a, rfl⟩
    rw [map_smul]
    obtain ⟨z, hzrep⟩ := Submodule.mkQ_surjective (boundary _ _ _).range
      (reduce d₂ d₃ h r a)
    rw [← hzrep, ← map_smul]
    have hz : r • z = 0 := by
      apply Subtype.ext
      exact ModScalar.smul_quotient r C₂ z.val
    rw [hz, map_zero]

def equivalence
    (hinj : Function.Injective (fun x : C₁ => r • x))
    (hsat : ∀ y : C₁, r • y ∈ d₂.range → y ∈ d₂.range) :
    ModScalar.Quotient r (Homology d₂ d₃ h) ≃ₗ[R] ReducedHomology d₂ d₃ h r :=
  (Submodule.quotEquivOfEq _ _ (by
    ext q
    exact (reduce_eq_zero_iff d₂ d₃ h r hinj q).symm)).trans
      ((reduce d₂ d₃ h r).quotKerEquivOfSurjective (reduce_surjective d₂ d₃ h r hsat))

end Parafree.Homology.ScalarReduction
