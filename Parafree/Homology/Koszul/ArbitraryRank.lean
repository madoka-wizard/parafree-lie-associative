import Parafree.Homology.Koszul.PolynomialVariables
import Parafree.Linear.ExteriorFiniteSupport

/-!
# Exactness of the polynomial Koszul complex in arbitrary rank

Cycles have finite exterior support. On a finite support the variable sequence
is weakly regular, and the finite-variable filling maps back to the original
complex. Coefficients stay in the full polynomial ring throughout, so no
finite-generation hypothesis on that ring is needed.
-/

noncomputable section

namespace Parafree.Homology.Koszul

open CategoryTheory ExteriorAlgebra MvPolynomial
open Parafree.Linear.ExteriorFiniteSupport

variable (R σ : Type*) [CommRing R]

abbrev Polynomial := MvPolynomial σ R

def variableMap : (σ →₀ Polynomial R σ) →ₗ[Polynomial R σ] Polynomial R σ :=
  Finsupp.linearCombination (Polynomial R σ) X

def finiteVariableMap (s : Finset σ) :
    (s →₀ Polynomial R σ) →ₗ[Polynomial R σ] Polynomial R σ :=
  (variableMap R σ).comp (inclusion (Polynomial R σ) σ s)

def variableList (s : Finset σ) : List (Polynomial R σ) := s.toList.map X

def enumeration (s : Finset σ) : Fin (variableList R σ s).length ≃ s := by
  classical
  exact (finCongr (List.length_map X)).trans
    ((List.Nodup.getEquiv s.toList s.nodup_toList).trans
      (Equiv.setCongr (by ext i; exact Finset.mem_toList)))

theorem enumeration_variable (s : Finset σ) (i : Fin (variableList R σ s).length) :
    X ((enumeration R σ s i).1) = (variableList R σ s).get i := by
  classical
  change X (s.toList.get ⟨i.1, by simpa only [variableList, List.length_map] using i.2⟩) =
    (s.toList.map X).get i
  simp

def listCoordinates (s : Finset σ) :
    (Fin (variableList R σ s).length → Polynomial R σ) ≃ₗ[Polynomial R σ]
      (s →₀ Polynomial R σ) :=
  (Finsupp.linearEquivFunOnFinite (Polynomial R σ) (Polynomial R σ) _).symm.trans
    (Finsupp.mapDomain.linearEquiv (Polynomial R σ) (Polynomial R σ) (enumeration R σ s))

theorem finiteVariableMap_coordinates (s : Finset σ) :
    (finiteVariableMap R σ s).comp (listCoordinates R σ s).toLinearMap =
      Fintype.linearCombination (Polynomial R σ) (variableList R σ s).get := by
  classical
  apply (Pi.basisFun (Polynomial R σ) (Fin (variableList R σ s).length)).ext
  intro i
  simp [finiteVariableMap, variableMap, listCoordinates, inclusion,
    Finsupp.lmapDomain_apply, enumeration_variable]

/-- The finite-support subcomplex is the ordinary Koszul complex of the
corresponding list of variables, in different coordinates. -/
def finiteComplexIso (s : Finset σ) :
    koszulComplex.ofList (variableList R σ s) ≅ koszulComplex (finiteVariableMap R σ s) :=
  koszulComplex.isoOfEquiv _ (listCoordinates R σ s) _ (finiteVariableMap_coordinates R σ s)

theorem finite_exactAt (s : Finset σ) (n : ℕ) (hn : n ≠ 0) :
    (koszulComplex (finiteVariableMap R σ s)).ExactAt n :=
  HomologicalComplex.ExactAt.of_iso
    (variables_exactAt s.toList s.nodup_toList n hn) (finiteComplexIso R σ s)

theorem finite_fill (s : Finset σ) (n : ℕ)
    (x : ⋀[Polynomial R σ]^(n + 1) (s →₀ Polynomial R σ))
    (hx : koszulComplex.d (finiteVariableMap R σ s) n x = 0) :
    ∃ y, koszulComplex.d (finiteVariableMap R σ s) (n + 1) y = x := by
  have he := finite_exactAt R σ s (n + 1) (Nat.succ_ne_zero n)
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at he
  change ∀ z, ((koszulComplex (finiteVariableMap R σ s)).d (n + 1) n).hom z = 0 →
    ∃ y, ((koszulComplex (finiteVariableMap R σ s)).d (n + 2) (n + 1)).hom y = z at he
  have hd : (koszulComplex (finiteVariableMap R σ s)).d (n + 2) (n + 1) =
      ModuleCat.ofHom (koszulComplex.d (finiteVariableMap R σ s) (n + 1)) :=
    koszulComplex.d_eq_d _ (n + 1)
  rw [koszulComplex.d_eq_d, hd] at he
  exact he x hx

theorem differential_inclusion (s : Finset σ) (n : ℕ)
    (x : ⋀[Polynomial R σ]^(n + 1) (s →₀ Polynomial R σ)) :
    koszulComplex.d (variableMap R σ) n (exteriorInclusion (Polynomial R σ) σ s (n + 1) x) =
      exteriorInclusion (Polynomial R σ) σ s n (koszulComplex.d (finiteVariableMap R σ s) n x) := by
  have h := koszulComplex.map_d_comm (finiteVariableMap R σ s)
    (inclusion (Polynomial R σ) σ s) (variableMap R σ) rfl n
  have hh : (koszulComplex.d (variableMap R σ) n).comp
      (exteriorInclusion (Polynomial R σ) σ s (n + 1)) =
      (exteriorInclusion (Polynomial R σ) σ s n).comp
        (koszulComplex.d (finiteVariableMap R σ s) n) := congrArg ModuleCat.Hom.hom h
  exact LinearMap.congr_fun hh x

/-- Every positive-degree polynomial Koszul cycle is a boundary, for an
arbitrary set of polynomial variables and an arbitrary commutative ring. -/
theorem fill (n : ℕ)
    (x : ⋀[Polynomial R σ]^(n + 1) (σ →₀ Polynomial R σ))
    (hx : koszulComplex.d (variableMap R σ) n x = 0) :
    ∃ y, koszulComplex.d (variableMap R σ) (n + 1) y = x := by
  obtain ⟨s, z, rfl⟩ := exists_lift (Polynomial R σ) σ (n + 1) x
  have hz : koszulComplex.d (finiteVariableMap R σ s) n z = 0 := by
    apply exteriorInclusion_injective (Polynomial R σ) σ s n
    rw [← differential_inclusion, hx, map_zero]
  obtain ⟨y, hy⟩ := finite_fill R σ s n z hz
  refine ⟨exteriorInclusion (Polynomial R σ) σ s (n + 2) y, ?_⟩
  rw [differential_inclusion, hy]

theorem exactAt (n : ℕ) (hn : n ≠ 0) : (koszulComplex (variableMap R σ)).ExactAt n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ z, ((koszulComplex (variableMap R σ)).d (k + 1) k).hom z = 0 →
    ∃ y, ((koszulComplex (variableMap R σ)).d (k + 2) (k + 1)).hom y = z
  have hd : (koszulComplex (variableMap R σ)).d (k + 2) (k + 1) =
      ModuleCat.ofHom (koszulComplex.d (variableMap R σ) (k + 1)) :=
    koszulComplex.d_eq_d _ (k + 1)
  rw [koszulComplex.d_eq_d, hd]
  exact fill R σ k

theorem homology_isZero (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero ((koszulComplex (variableMap R σ)).homology n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (exactAt R σ n hn)

end Parafree.Homology.Koszul
