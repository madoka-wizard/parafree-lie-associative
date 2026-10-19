import Parafree.Homology.Coefficients.Functoriality

/-! Elementwise exactness and transport along coefficient-module equivalences. -/

noncomputable section

namespace Parafree.Homology.Coefficients

open CategoryTheory
open scoped TensorProduct
open Parafree.Linear.ExteriorTensor (Chain)

universe u v w w'
variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {M : Type w} {N : Type w'}
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem exactAt_succ_iff_fill (n : ℕ) :
    (complex R L M).ExactAt (n + 1) ↔
      ∀ x, differential R L M n x = 0 → ∃ y, differential R L M (n + 1) y = x := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hd : (complex R L M).d (n + 2) (n + 1) =
      ModuleCat.ofHom (differential R L M (n + 1)) := complex_d R L M (n + 1)
  change (∀ x, ((complex R L M).d (n + 1) n).hom x = 0 →
    ∃ y, ((complex R L M).d (n + 2) (n + 1)).hom y = x) ↔ _
  rw [complex_d, hd]
  rfl

def chainEquiv (e : M ≃ₗ⁅R,L⁆ N) (n : ℕ) : Chain R L M n ≃ₗ[R] Chain R L N n :=
  TensorProduct.congr (LinearEquiv.refl R _) e.toLinearEquiv

theorem chainEquiv_differential (e : M ≃ₗ⁅R,L⁆ N) (n : ℕ) (x : Chain R L M (n + 1)) :
    chainEquiv e n (differential R L M n x) =
      differential R L N n (chainEquiv e (n + 1) x) :=
  chainMap_differential_apply e.toLieModuleHom n x

/-- Transfer an actual cycle-filling result across an equivariant coefficient equivalence. -/
theorem fill_of_equiv (e : M ≃ₗ⁅R,L⁆ N) (n : ℕ)
    (hfill : ∀ x, differential R L N n x = 0 → ∃ y, differential R L N (n + 1) y = x)
    (x : Chain R L M (n + 1)) (hx : differential R L M n x = 0) :
    ∃ y, differential R L M (n + 1) y = x := by
  have hc : differential R L N n (chainEquiv e (n + 1) x) = 0 := by
    rw [← chainEquiv_differential, hx, map_zero]
  obtain ⟨y, hy⟩ := hfill (chainEquiv e (n + 1) x) hc
  refine ⟨(chainEquiv e (n + 2)).symm y, ?_⟩
  apply (chainEquiv e (n + 1)).injective
  rw [chainEquiv_differential, LinearEquiv.apply_symm_apply, hy]

theorem exactAt_of_equiv (e : M ≃ₗ⁅R,L⁆ N) (n : ℕ) (hn : n ≠ 0)
    (h : (complex R L N).ExactAt n) : (complex R L M).ExactAt n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [exactAt_succ_iff_fill] at h ⊢
  exact fill_of_equiv e k h

section Categorical

variable {N' : Type w} [AddCommGroup N'] [Module R N']
  [LieRingModule L N'] [LieModule R L N']

/-- An equivariant coefficient equivalence induces an isomorphism of CE complexes. -/
def coefficientComplexIso (e : M ≃ₗ⁅R,L⁆ N') : complex R L M ≅ complex R L N' :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (chainEquiv e n).toModuleIso)
    (fun i j hij => by
      have h : j + 1 = i := hij
      subst i
      rw [complex_d, complex_d]
      ext c
      exact (chainEquiv_differential e j c).symm)

/-- Transport the actual categorical homology, in every degree. -/
def coefficientHomologyEquiv (e : M ≃ₗ⁅R,L⁆ N') (n : ℕ) :
    Homology R L M n ≃ₗ[R] Homology R L N' n :=
  (HomologicalComplex.homologyMapIso (coefficientComplexIso e) n).toLinearEquiv

end Categorical

end Parafree.Homology.Coefficients
