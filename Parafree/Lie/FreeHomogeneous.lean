import Parafree.Lie.FreeTruncation
import Parafree.Lie.LowerCentralLayers

/-! The integral free Lie algebra is the finite direct sum of its homogeneous
word-length components. The construction uses PBW coordinates, not a Hall basis. -/

noncomputable section
namespace Parafree.Lie.FreeHomogeneous

open LieRings FreeLieDimension

variable (X : Type*)

abbrev Free := FreeLieAlgebra ℤ X
abbrev Words := FreeMonoid X →₀ ℤ

def coordinates : Free X →ₗ[ℤ] Words X :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap.comp
    (PBW.freeLieToFreeAlgebra ℤ X).toLinearMap

theorem coordinates_injective : Function.Injective (coordinates X) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective.comp
    (freeLieToFreeAlgebra_injective_int X)

/-- The component of word length `n`, defined inside the actual free Lie ring. -/
def component (n : ℕ) : Submodule ℤ (Free X) :=
  (Finsupp.supported ℤ ℤ {w : FreeMonoid X | w.length = n}).comap (coordinates X)

def wordProjection (n : ℕ) : Words X →ₗ[ℤ] Words X where
  toFun := Finsupp.filter (fun w : FreeMonoid X => w.length = n)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

theorem wordProjection_component (n : ℕ) (x : component X n) :
    wordProjection X n (coordinates X x) = coordinates X x := by
  apply (Finsupp.filter_eq_self_iff _ _).mpr
  intro w hw
  exact x.property (Finsupp.mem_support_iff.mpr hw)

theorem wordProjection_component_ne (n m : ℕ) (h : n ≠ m) (x : component X m) :
    wordProjection X n (coordinates X x) = 0 := by
  apply (Finsupp.filter_eq_zero_iff _ _).mpr
  intro w hw
  by_contra hx
  exact h (hw.symm.trans (x.property (Finsupp.mem_support_iff.mpr hx)))

abbrev Components := Π₀ n, component X n

def sumComponents : Components X →ₗ[ℤ] Free X :=
  DFinsupp.lsum ℤ (fun n => (component X n).subtype)

@[simp] theorem sumComponents_single (n : ℕ) (x : component X n) :
    sumComponents X (DFinsupp.single n x) = x :=
  DFinsupp.lsum_single ℤ (fun n => (component X n).subtype) n x

/-- Ambient projection of a sum recovers precisely its specified component. -/
theorem projection_sum (n : ℕ) (x : Components X) :
    wordProjection X n (coordinates X (sumComponents X x)) = coordinates X (x n) := by
  have h : (wordProjection X n).comp ((coordinates X).comp (sumComponents X)) =
      (coordinates X).comp ((component X n).subtype.comp (DFinsupp.lapply n)) := by
    apply DFinsupp.lhom_ext
    intro m a
    simp only [LinearMap.comp_apply, sumComponents_single, Submodule.subtype_apply,
      DFinsupp.lapply_apply]
    by_cases h : n = m
    · subst m
      rw [DFinsupp.single_eq_same]
      exact wordProjection_component X n a
    · rw [DFinsupp.single_eq_of_ne h]
      exact (wordProjection_component_ne X n m h a).trans (map_zero _).symm
  exact LinearMap.congr_fun h x

theorem sumComponents_injective : Function.Injective (sumComponents X) := by
  intro x y h
  ext n
  apply (coordinates_injective X)
  rw [← projection_sum, ← projection_sum, h]

theorem mk_single_mem_component (w : FreeMagma X) (c : ℤ) :
    freeLieMkLinear X (Finsupp.single w c) ∈ component X w.length := by
  have h := (associativeExact X w.length).smul_mem c
    (magmaToFreeAlgebra_single_mem_exact X w)
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (PBW.freeLieToFreeAlgebra ℤ X (freeLieMkLinear X (Finsupp.single w c))) ∈
      Finsupp.supported ℤ ℤ {v : FreeMonoid X | v.length = w.length}
  rw [freeLieToFreeAlgebra_mk]
  change magmaToFreeAlgebra X (Finsupp.single w c) ∈ associativeExact X w.length
  have hc : c • (Finsupp.single w 1 : FreeNonUnitalNonAssocAlgebra ℤ X) =
      Finsupp.single w c := by
    change c • (Finsupp.single w 1 : FreeMagma X →₀ ℤ) = _
    rw [Finsupp.smul_single]
    simp only [smul_eq_mul, mul_one]
  rw [← hc]
  exact (magmaToFreeAlgebra X).map_smul c (Finsupp.single w 1) ▸ h

theorem sumComponents_surjective : Function.Surjective (sumComponents X) := by
  have h : ∀ p : FreeNonUnitalNonAssocAlgebra ℤ X,
      freeLieMkLinear X p ∈ LinearMap.range (sumComponents X) := by
    intro p
    induction p using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using (LinearMap.range (sumComponents X)).zero_mem
    | add p q hp hq =>
      simpa only [map_add] using (LinearMap.range (sumComponents X)).add_mem hp hq
    | single w c =>
      exact ⟨DFinsupp.single w.length ⟨_, mk_single_mem_component X w c⟩,
        sumComponents_single X _ _⟩
  intro x
  obtain ⟨p, rfl⟩ := Quot.mk_surjective x
  exact h p

/-- A finite homogeneous decomposition, valid for any generator type. -/
def sumEquiv : Components X ≃ₗ[ℤ] Free X :=
  LinearEquiv.ofBijective (sumComponents X)
    ⟨sumComponents_injective X, sumComponents_surjective X⟩

@[simp] theorem sumEquiv_symm_component (n : ℕ) (x : component X n) :
    (sumEquiv X).symm x = DFinsupp.single n x := by
  apply (sumEquiv X).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (sumComponents_single X n x).symm

/-- The intrinsic homogeneous projection in the free Lie ring. -/
def projection (n : ℕ) : Free X →ₗ[ℤ] Free X :=
  (component X n).subtype.comp ((DFinsupp.lapply n).comp (sumEquiv X).symm.toLinearMap)

theorem projection_mem (n : ℕ) (x : Free X) : projection X n x ∈ component X n :=
  ((sumEquiv X).symm x n).property

theorem coordinates_projection (n : ℕ) (x : Free X) :
    coordinates X (projection X n x) = wordProjection X n (coordinates X x) := by
  have h := projection_sum X n ((sumEquiv X).symm x)
  change wordProjection X n (coordinates X ((sumEquiv X) ((sumEquiv X).symm x))) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem projection_of_mem (n : ℕ) (x : component X n) : projection X n x = x := by
  apply coordinates_injective X
  rw [coordinates_projection, wordProjection_component]

theorem component_lie {i j : ℕ} {x y : Free X}
    (hx : x ∈ component X i) (hy : y ∈ component X j) :
    ⁅x, y⁆ ∈ component X (i + j) := by
  change PBW.freeLieToFreeAlgebra ℤ X ⁅x, y⁆ ∈ associativeExact X (i + j)
  rw [LieHom.map_lie]
  exact associativeExact_lie X hx hy

end Parafree.Lie.FreeHomogeneous
