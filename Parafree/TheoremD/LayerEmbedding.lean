import Parafree.TheoremD.KernelBasis
import Parafree.TheoremD.ExtendedEncoding
import Parafree.Associative.FreeWords

/-! Faithful linear models of the successive kernel-power layers in a free
associative algebra. The extra letters serve as separators between factors. -/
noncomputable section
namespace Parafree.TheoremD.LayerEmbedding
open Parafree.TheoremC
open Parafree.Associative FreeAugmentation
open NormalWords NormalRepresentation NormalBasis NormalFiltration
variable (k : Type*) [CommRing k]

abbrev Target := FreeAlgebra k TargetLetter

def part (h : ℕ) : Space k →ₗ[k] Space k where
  toFun := Finsupp.filter (fun w => countZ w.val = h)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

@[simp] theorem part_apply (h : ℕ) (v : Space k) (w : BasisWord) :
    part k h v w = if countZ w.val = h then v w else 0 := Finsupp.filter_apply _ _ _

@[simp] theorem part_basis (h : ℕ) (w : BasisWord) :
    part k h (basis k w) = if countZ w.val = h then basis k w else 0 := by
  by_cases hw : countZ w.val = h
  · simp [part, basis, hw]
  · simp [part, basis, hw]

theorem part_zero_iff (h : ℕ) (v : Space k) :
    part k h v = 0 ↔ ∀ w : BasisWord, countZ w.val = h → v w = 0 := by
  constructor
  · intro he w hw
    have hh := congrArg (fun f : Space k => f w) he
    simpa [hw] using hh
  · intro he
    ext w
    by_cases hw : countZ w.val = h <;> simp [hw, he]

theorem part_zero_iff_mem_succ (h : ℕ) {v : Space k} (hv : v ∈ level k h) :
    part k h v = 0 ↔ v ∈ level k (h+1) := by
  rw [part_zero_iff, mem_level_iff]
  constructor
  · intro he w hw
    by_cases hl : countZ w.val < h
    · exact (mem_level_iff k h v).mp hv w hl
    · exact he w (by omega)
  · intro he w hw
    exact he w (by omega)

def encodedWord (w : BasisWord) : Target k := word k TargetLetter (encodeExtended w.val)
def encodeLinear : Space k →ₗ[k] Target k := Finsupp.linearCombination k (encodedWord k)

@[simp] theorem encodeLinear_basis (w : BasisWord) : encodeLinear k (basis k w) = encodedWord k w := by
  simp [encodeLinear, basis]

theorem encodeLinear_injective : Function.Injective (encodeLinear k) := by
  apply linearIndependent_iff_injective_finsuppLinearCombination.mp
  apply (FreeAlgebra.basisFreeMonoid k TargetLetter).linearIndependent.comp
    (fun w : BasisWord => FreeMonoid.ofList (encodeExtended w.val))
  intro v w h
  exact encodeExtended_injective (congrArg FreeMonoid.toList h)

def rawPart (h : ℕ) : Space k →ₗ[k] Target k := (encodeLinear k).comp (part k h)

@[simp] theorem rawPart_basis (h : ℕ) (w : BasisWord) :
    rawPart k h (basis k w) = if countZ w.val = h then encodedWord k w else 0 := by
  simp only [rawPart, LinearMap.comp_apply, part_basis]
  split <;> simp_all

def rawLayer (h : ℕ) : A₀ k →ₗ[k] Target k := (rawPart k h).comp (represent k)

def translation : Target k ≃ₐ[k] Target k :=
  shiftEquiv k TargetLetter (fun i => match i with | Sum.inl _ => 1 | Sum.inr _ => 0)

def layer (h : ℕ) : A₀ k →ₗ[k] Target k := (translation k).toLinearMap.comp (rawLayer k h)

/-- The layer detector has precisely the next kernel power as kernel when
restricted to the current kernel power. -/
theorem layer_zero_iff (h : ℕ) {a : A₀ k} (ha : a ∈ kernel k ^ h) :
    layer k h a = 0 ↔ a ∈ kernel k ^ (h+1) := by
  change translation k (encodeLinear k (part k h (represent k a))) = 0 ↔ _
  rw [map_eq_zero_iff _ (translation k).injective,
    map_eq_zero_iff _ (encodeLinear_injective k)]
  rw [part_zero_iff_mem_succ k h ((KernelBasis.mem_kernel_power_iff k h a).mp ha),
    KernelBasis.mem_kernel_power_iff]

end Parafree.TheoremD.LayerEmbedding
