import Parafree.Homology.Coefficients.Functoriality
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Short exact coefficient sequences and their connecting maps.

Exactness is proved on tensor chain modules, then transported through Mathlib's
long exact homology sequence. Two independent sufficient hypotheses are exposed:
flat exterior powers, or a linear retraction of the first coefficient map.
The latter need not commute with the Lie action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Parafree.Homology.Coefficients

open Parafree.Linear.ExteriorTensor

universe u v w
variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {M N P : Type w}
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

@[simp] theorem complexMap_zero : complexMap (0 : M →ₗ⁅R,L⁆ N) = 0 := by
  ext n c
  change chainMap (0 : M →ₗ⁅R,L⁆ N) n c = 0
  induction c using TensorProduct.induction_on with
  | zero => exact map_zero _
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | tmul u m => simp only [chainMap_tmul, LieModuleHom.zero_apply, TensorProduct.tmul_zero]

/-- A pair of coefficient maps gives a short complex of CE complexes. -/
def sequence (f : M →ₗ⁅R,L⁆ N) (g : N →ₗ⁅R,L⁆ P) (hfg : g.comp f = 0) :
    ShortComplex (ChainComplex (ModuleCat.{max u v w} R) ℕ) :=
  ShortComplex.mk (complexMap f) (complexMap g) (by rw [← complexMap_comp, hfg, complexMap_zero])

variable (f : M →ₗ⁅R,L⁆ N) (g : N →ₗ⁅R,L⁆ P)

omit [LieModule R L M] [LieModule R L N] [LieModule R L P] in
theorem chainMap_exact (h : Function.Exact f g) (hg : Function.Surjective g) (n : ℕ) :
    Function.Exact (chainMap f n) (chainMap g n) :=
  _root_.lTensor_exact (⋀[R]^n L) h hg

omit [LieModule R L N] [LieModule R L P] in
theorem chainMap_surjective (hg : Function.Surjective g) (n : ℕ) :
    Function.Surjective (chainMap g n) :=
  LinearMap.lTensor_surjective (⋀[R]^n L) hg

omit [LieModule R L M] [LieModule R L N] in
theorem chainMap_injective_of_flat (hf : Function.Injective f) (n : ℕ)
    [Module.Flat R (⋀[R]^n L)] : Function.Injective (chainMap f n) :=
  Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf

omit [LieModule R L M] [LieModule R L N] in
theorem chainMap_injective_of_retraction (r : N →ₗ[R] M)
    (hr : r.comp f.toLinearMap = LinearMap.id) (n : ℕ) :
    Function.Injective (chainMap f n) := by
  have h : (r.lTensor (⋀[R]^n L)).comp (chainMap f n) = LinearMap.id := by
    change (r.lTensor (⋀[R]^n L)).comp (f.toLinearMap.lTensor (⋀[R]^n L)) = _
    rw [← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id]
  exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun h x)

/-- The only additional input beyond coefficient exactness is injectivity after tensoring. -/
theorem sequence_shortExact (hfg : g.comp f = 0)
    (h : Function.Exact f g) (hg : Function.Surjective g)
    (hf : ∀ n, Function.Injective (chainMap f n)) : (sequence f g hfg).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact chainMap_exact f g h hg n
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact hf n
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact chainMap_surjective g hg n

theorem sequence_shortExact_of_flat [∀ n : ℕ, Module.Flat R (⋀[R]^n L)]
    (hfg : g.comp f = 0) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (sequence f g hfg).ShortExact :=
  sequence_shortExact f g hfg h hg (fun n => chainMap_injective_of_flat f hf n)

/-- An underlying linear splitting suffices; no equivariant splitting is required. -/
theorem sequence_shortExact_of_retraction (hfg : g.comp f = 0)
    (h : Function.Exact f g) (hg : Function.Surjective g)
    (r : N →ₗ[R] M) (hr : r.comp f.toLinearMap = LinearMap.id) :
    (sequence f g hfg).ShortExact :=
  sequence_shortExact f g hfg h hg (chainMap_injective_of_retraction f r hr)

/-- The free underlying Lie module case, including integral based Lie algebras. -/
theorem sequence_shortExact_of_free [Module.Free R L]
    (hfg : g.comp f = 0) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (sequence f g hfg).ShortExact :=
  sequence_shortExact_of_flat f g hfg h hf hg

variable {f g}

/-- The connecting morphism lowers homological degree by one. -/
def connecting {hfg : g.comp f = 0} (hS : (sequence f g hfg).ShortExact) (n : ℕ) :
    homology R L P (n + 1) ⟶ homology R L M n :=
  hS.δ (n + 1) n rfl

theorem homology_exact {hfg : g.comp f = 0} (hS : (sequence f g hfg).ShortExact) (n : ℕ) :
    Function.Exact (homologyMap f n) (homologyMap g n) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.homology_exact₂ n)

theorem connecting_exact_left {hfg : g.comp f = 0}
    (hS : (sequence f g hfg).ShortExact) (n : ℕ) :
    Function.Exact (connecting hS n) (homologyMap f n) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hS.homology_exact₁ (n + 1) n rfl)

theorem connecting_exact_right {hfg : g.comp f = 0}
    (hS : (sequence f g hfg).ShortExact) (n : ℕ) :
    Function.Exact (homologyMap g (n + 1)) (connecting hS n) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hS.homology_exact₃ (n + 1) n rfl)

/-- Dimension shifting requires both adjacent middle homologies to vanish. -/
def dimensionShift {hfg : g.comp f = 0} (hS : (sequence f g hfg).ShortExact) (n : ℕ)
    (hi : IsZero (homology R L N (n + 1))) (hj : IsZero (homology R L N n)) :
    Homology R L P (n + 1) ≃ₗ[R] Homology R L M n :=
  (hS.δIso (n + 1) n rfl hi hj).toLinearEquiv

end Parafree.Homology.Coefficients
