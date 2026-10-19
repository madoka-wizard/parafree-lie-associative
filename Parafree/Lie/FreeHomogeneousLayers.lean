import Parafree.Lie.FreeHomogeneous

/-! The canonical homogeneous representative of each lower-central layer of
an integral free Lie algebra. -/

noncomputable section
namespace Parafree.Lie.FreeHomogeneous

variable (X : Type*)

/-- Lower-central membership is exactly vanishing of all short word coordinates. -/
theorem mem_lowerCentral_iff (n : ℕ) (x : Free X) :
    x ∈ lowerCentral ℤ (Free X) n ↔
      ∀ w : FreeMonoid X, w.length ≤ n → coordinates X x w = 0 := by
  rw [← FreeTruncation.coordinates_eq_zero_iff]
  change Finsupp.filter (fun w : FreeMonoid X => w.length ≤ n) (coordinates X x) = 0 ↔ _
  exact Finsupp.filter_eq_zero_iff _ _

theorem component_mem_lowerCentral (n : ℕ) (x : component X (n + 1)) :
    (x : Free X) ∈ lowerCentral ℤ (Free X) n := by
  apply (mem_lowerCentral_iff X n x).mpr
  intro w hw
  by_contra h
  have he := x.property (Finsupp.mem_support_iff.mpr h)
  change w.length = n + 1 at he
  omega

theorem component_eq_zero_of_lowerCentral (n : ℕ) (x : component X n)
    (hx : (x : Free X) ∈ lowerCentral ℤ (Free X) n) : (x : Free X) = 0 := by
  apply coordinates_injective X
  rw [map_zero]
  ext w
  change coordinates X x w = 0
  by_contra h
  have he := x.property (Finsupp.mem_support_iff.mpr h)
  exact h ((mem_lowerCentral_iff X n x).mp hx w he.le)

/-- A lower-central element has no homogeneous component of this or lower degree. -/
theorem projection_eq_zero_of_lowerCentral (n : ℕ) (x : Free X)
    (hx : x ∈ lowerCentral ℤ (Free X) n) : projection X n x = 0 := by
  apply coordinates_injective X
  rw [coordinates_projection, map_zero]
  change Finsupp.filter (fun w : FreeMonoid X => w.length = n) (coordinates X x) = 0
  apply (Finsupp.filter_eq_zero_iff _ _).mpr
  intro w hw
  exact (mem_lowerCentral_iff X n x).mp hx w hw.le

theorem homogeneousComponent_eq_zero_of_lowerCentral (n : ℕ) (x : Free X)
    (hx : x ∈ lowerCentral ℤ (Free X) n) : (sumEquiv X).symm x n = 0 :=
  Subtype.ext (projection_eq_zero_of_lowerCentral X n x hx)
/-- The free Lie algebra has no degree-zero component. -/
theorem component_zero (x : component X 0) : (x : Free X) = 0 :=
  component_eq_zero_of_lowerCentral X 0 x (LieSubmodule.mem_top _)

/-- Removing the leading homogeneous term raises the lower-central depth. -/
theorem sub_projection_mem (n : ℕ) (x : lowerCentral ℤ (Free X) n) :
    (x : Free X) - projection X (n + 1) x ∈ lowerCentral ℤ (Free X) (n + 1) := by
  apply (mem_lowerCentral_iff X (n + 1) _).mpr
  intro w hw
  rw [map_sub, Finsupp.sub_apply, coordinates_projection]
  change coordinates X x w -
    Finsupp.filter (fun w : FreeMonoid X => w.length = n + 1) (coordinates X x) w = 0
  by_cases he : w.length = n + 1
  · rw [Finsupp.filter_apply_pos (fun v : FreeMonoid X => v.length = n + 1) _ he, sub_self]
  · rw [Finsupp.filter_apply_neg (fun v : FreeMonoid X => v.length = n + 1) _ he, sub_zero]
    exact (mem_lowerCentral_iff X n x).mp x.property w (by omega)

def componentToLayer (n : ℕ) :
    component X (n + 1) →ₗ[ℤ] LowerCentralLayer ℤ (Free X) n :=
  (layerRelations ℤ (Free X) n).mkQ.comp
    ((component X (n + 1)).subtype.codRestrict _ (component_mem_lowerCentral X n))

theorem componentToLayer_injective (n : ℕ) : Function.Injective (componentToLayer X n) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have hnext : (x : Free X) ∈ lowerCentral ℤ (Free X) (n + 1) :=
    (Submodule.Quotient.mk_eq_zero (layerRelations ℤ (Free X) n)).mp hx
  exact Subtype.ext (component_eq_zero_of_lowerCentral X (n + 1) x hnext)

theorem componentToLayer_surjective (n : ℕ) : Function.Surjective (componentToLayer X n) := by
  intro x
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (layerRelations ℤ (Free X) n) x
  refine ⟨⟨projection X (n + 1) a, projection_mem X (n + 1) a⟩, ?_⟩
  apply (Submodule.Quotient.eq (layerRelations ℤ (Free X) n)).mpr
  change projection X (n + 1) a - (a : Free X) ∈ lowerCentral ℤ (Free X) (n + 1)
  simpa only [neg_sub] using (lowerCentral ℤ (Free X) (n + 1)).neg_mem (sub_projection_mem X n a)

/-- Homogeneous elements give exactly the specified lower-central quotient. -/
def layerEquiv (n : ℕ) :
    component X (n + 1) ≃ₗ[ℤ] LowerCentralLayer ℤ (Free X) n :=
  LinearEquiv.ofBijective (componentToLayer X n)
    ⟨componentToLayer_injective X n, componentToLayer_surjective X n⟩

theorem layerEquiv_apply (n : ℕ) (x : component X (n + 1)) :
    layerEquiv X n x = Submodule.Quotient.mk
      (⟨x, component_mem_lowerCentral X n x⟩ : lowerCentral ℤ (Free X) n) := rfl

/-- Additive induction using positive homogeneous pieces only. -/
theorem homogeneous_induction (P : Free X → Prop) (hzero : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hhom : ∀ n (x : component X (n + 1)), P x) (x : Free X) : P x := by
  obtain ⟨a, rfl⟩ := sumComponents_surjective X x
  induction a using DFinsupp.induction with
  | h0 => simpa only [map_zero] using hzero
  | @ha n a b _ _ ih =>
    rw [map_add, sumComponents_single]
    apply hadd _ _ _ ih
    cases n with
    | zero => simpa only [component_zero X a] using hzero
    | succ n => exact hhom n a

end Parafree.Lie.FreeHomogeneous
