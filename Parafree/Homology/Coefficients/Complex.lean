import Parafree.Homology.Coefficients.Exterior
import Parafree.Linear.ExteriorTensorGrading
import LieRings.Homological.LieHomology.Complex

/-! The coefficient CE chain complex in every degree, over an arbitrary commutative ring. -/

noncomputable section

open CategoryTheory

namespace Parafree.Homology.Coefficients

open scoped TensorProduct
open Parafree.Linear.ExteriorTensor

universe u v w
variable (R : Type u) (L : Type v) (M : Type w) [CommRing R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

theorem prepend_mem_component (x : L) {n : ℕ} {t : Total R L M}
    (ht : t ∈ component R L M n) : prepend R L M x t ∈ component R L M (n + 1) := by
  obtain ⟨c, rfl⟩ := ht
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb => simp only [map_add]; exact Submodule.add_mem _ ha hb
  | tmul z m =>
    rw [inclusion_tmul, prepend_tmul]
    apply tmul_mem_component
    have hx : ExteriorAlgebra.ι R x ∈ ⋀[R]^1 L := by
      simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι R) x
    simpa only [Nat.one_add] using SetLike.mul_mem_graded hx z.property

variable [LieRingModule L M] [LieModule R L M]

theorem action_mem_component (x : L) {n : ℕ} {t : Total R L M}
    (ht : t ∈ component R L M n) : action R L M x t ∈ component R L M n := by
  obtain ⟨c, rfl⟩ := ht
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb => simp only [map_add]; exact Submodule.add_mem _ ha hb
  | tmul z m =>
    rw [inclusion_tmul, action_tmul]
    exact Submodule.add_mem _
      (tmul_mem_component R L M
        (LieRings.Homological.LieHomology.adExterior_mem_exteriorPower R L x z.property) m)
      (tmul_mem_component R L M z.property ⁅x, m⁆)

theorem boundary_eq_zero_of_exterior_zero {u : ExteriorAlgebra R L}
    (hu : u ∈ ⋀[R]^0 L) (m : M) : boundary R L M (u ⊗ₜ[R] m) = 0 := by
  change u ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ 0 at hu
  rw [pow_zero] at hu
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hu
  exact boundary_algebraMap_tmul R L M r m

theorem boundary_tmul_mem_component {n : ℕ} {u : ExteriorAlgebra R L}
    (hu : u ∈ ⋀[R]^n L) (m : M) :
    boundary R L M (u ⊗ₜ[R] m) ∈ component R L M (n - 1) := by
  induction hu using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [boundary_algebraMap_tmul]
    exact Submodule.zero_mem _
  | add a b i ha hb hda hdb =>
    rw [TensorProduct.add_tmul, map_add]
    exact Submodule.add_mem _ hda hdb
  | mem_mul a ha i u hu hdu =>
    obtain ⟨x, rfl⟩ := ha
    rw [← prepend_tmul, boundary_prepend]
    cases i with
    | zero =>
      rw [boundary_eq_zero_of_exterior_zero R L M hu m, map_zero, sub_zero]
      exact action_mem_component R L M x (tmul_mem_component R L M hu m)
    | succ i =>
      apply Submodule.sub_mem
      · exact action_mem_component R L M x (tmul_mem_component R L M hu m)
      · exact prepend_mem_component R L M x hdu

theorem boundary_mem_component {n : ℕ} {t : Total R L M}
    (ht : t ∈ component R L M n) : boundary R L M t ∈ component R L M (n - 1) := by
  obtain ⟨c, rfl⟩ := ht
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb => simp only [map_add]; exact Submodule.add_mem _ ha hb
  | tmul z m => exact boundary_tmul_mem_component R L M z.property m

/-- The differential with the upstream negative-bracket sign convention. -/
def differential (n : ℕ) : Chain R L M (n + 1) →ₗ[R] Chain R L M n :=
  -((projection R L M n).comp ((boundary R L M).comp (inclusion R L M (n + 1))))

theorem inclusion_differential (n : ℕ) (c : Chain R L M (n + 1)) :
    inclusion R L M n (differential R L M n c) =
      -boundary R L M (inclusion R L M (n + 1) c) := by
  change inclusion R L M n (-(projection R L M n
    (boundary R L M (inclusion R L M (n + 1) c)))) = _
  rw [map_neg]
  congr 1
  exact inclusion_projection R L M (n := n)
    (boundary_mem_component R L M (n := n + 1)
      (LinearMap.mem_range_self (inclusion R L M (n + 1)) c))

theorem differential_comp_differential (n : ℕ) :
    (differential R L M n).comp (differential R L M (n + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply inclusion_injective R L M n
  change inclusion R L M n (differential R L M n (differential R L M (n + 1) c)) =
    inclusion R L M n 0
  rw [inclusion_differential, inclusion_differential, map_neg, boundary_boundary,
    neg_zero, neg_zero, map_zero]

abbrev chains (n : ℕ) : ModuleCat.{max u v w} R := ModuleCat.of R (Chain R L M n)

theorem differential_sq (n : ℕ) :
    ModuleCat.ofHom (differential R L M (n + 1)) ≫
      ModuleCat.ofHom (differential R L M n) = 0 := by
  apply ModuleCat.hom_ext
  exact differential_comp_differential R L M n

/-- The all-degree coefficient CE complex. -/
def complex : ChainComplex (ModuleCat.{max u v w} R) ℕ :=
  ChainComplex.of (chains R L M)
    (fun n => ModuleCat.ofHom (differential R L M n)) (differential_sq R L M)

@[simp] theorem complex_X (n : ℕ) : (complex R L M).X n = chains R L M n := rfl

@[simp] theorem complex_d (n : ℕ) :
    (complex R L M).d (n + 1) n = ModuleCat.ofHom (differential R L M n) :=
  ChainComplex.of_d _ _ _ _

abbrev homology (n : ℕ) : ModuleCat.{max u v w} R := (complex R L M).homology n

/-- Coefficient CE homology as the underlying module of categorical chain homology. -/
abbrev Homology (n : ℕ) := (homology R L M n : Type (max u v w))

end Parafree.Homology.Coefficients
