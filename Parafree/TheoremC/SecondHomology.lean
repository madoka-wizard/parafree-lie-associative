import Parafree.TheoremC.FreeResolution
import Parafree.TheoremC.ReducedDifferential

/-! Actual second Tor with trivial coefficients, computed from a certified
projective resolution and naturally viewed as a module over the base ring. -/
noncomputable section
namespace Parafree.TheoremC
open CategoryTheory Parafree.Associative
universe u
variable (k : Type u) [CommRing k]

def homology (n : ℕ) : ModuleCat.{u} k :=
  DerivedCoinvariants.coefficientHomology (augmentation k) n

namespace SecondHomology
open PresentationComplex

def functor : ModuleCat.{u} (A k) ⥤ ModuleCat.{u} k :=
  DerivedCoinvariants.coefficientFunctor (augmentation k)

instance : (functor k).Additive :=
  inferInstanceAs (DerivedCoinvariants.coefficientFunctor (augmentation k)).Additive

/-- The quotient and restriction-of-scalars structures agree under augmentation. -/
def freeEquiv (ι : Type) : (functor k).obj (ModuleCat.of (A k) (ι →₀ A k)) ≃ₗ[k] (ι →₀ k) where
  __ := (CoinvariantsFree.equiv (augmentation k) ι).toAddEquiv
  map_smul' r x := by
    obtain ⟨v,rfl⟩ := (CoinvariantsFree.relations (augmentation k) ι).mkQ_surjective x
    change CoinvariantsFree.reduce (augmentation k) ι ((algebraMap k (A k) r) • v) =
      r • CoinvariantsFree.reduce (augmentation k) ι v
    rw [CoinvariantsFree.reduce_smul, AlgHom.commutes, Algebra.algebraMap_self]
    rfl

def secondMap := (functor k).map (ModuleCat.ofHom (d₂ k))

theorem freeEquiv_secondMap (x : (functor k).obj (ModuleCat.of (A k) (P₂ k))) :
    freeEquiv k (Fin 6) (secondMap k x) =
      ReducedDifferential.differential k (freeEquiv k ℕ x) := by
  obtain ⟨v,rfl⟩ := (CoinvariantsFree.relations (augmentation k) ℕ).mkQ_surjective x
  exact ReducedDifferential.reduce_d₂ k v

/-- The categorical differential has exactly the explicitly computed kernel. -/
def cyclesEquiv : LinearMap.ker (secondMap k).hom ≃ₗ[k]
    LinearMap.ker (ReducedDifferential.differential k) where
  toFun x := ⟨freeEquiv k ℕ x.val, by
    change ReducedDifferential.differential k (freeEquiv k ℕ x.val) = 0
    rw [← freeEquiv_secondMap, x.property, map_zero]⟩
  invFun y := ⟨(freeEquiv k ℕ).symm y.val, by
    apply (freeEquiv k (Fin 6)).injective
    rw [freeEquiv_secondMap, LinearEquiv.apply_symm_apply, map_zero]
    exact y.property⟩
  left_inv x := Subtype.ext ((freeEquiv k ℕ).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((freeEquiv k ℕ).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (map_smul _ _ _)

def complex : ChainComplex (ModuleCat.{u} k) ℕ :=
  ((functor k).mapHomologicalComplex _).obj (FreeResolution.complex k)

def shortComplex : ShortComplex (ModuleCat.{u} k) := (complex k).sc' 3 2 1

theorem shortComplex_f : (shortComplex k).f = 0 := by
  change (functor k).map ((FreeResolution.complex k).d 3 2) = 0
  have hd : (FreeResolution.complex k).d 3 2 = 0 :=
    ChainComplex.of_d (FreeResolution.objects k) (FreeResolution.differential k)
      (FreeResolution.differential_sq k) 2
  rw [hd, Functor.map_zero]

theorem boundaries_eq_bot : LinearMap.range (shortComplex k).moduleCatToCycles = ⊥ := by
  rw [LinearMap.range_eq_bot]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (shortComplex k).f x = 0
  rw [shortComplex_f]
  rfl

/-- Comparison with the actual left derived functor, followed by the ordinary
kernel/image description of degree-two homology. -/
def homologyCyclesEquiv : homology k 2 ≃ₗ[k] LinearMap.ker (secondMap k).hom := by
  let e := (FreeResolution.resolution k).isoLeftDerivedObj (functor k) 2
  let c := (complex k).homologyIsoSc' 3 2 1 (by simp) (by simp)
  let q := (shortComplex k).moduleCatHomologyIso
  let z := (LinearMap.range (shortComplex k).moduleCatToCycles).quotEquivOfEqBot
    (boundaries_eq_bot k)
  exact (e ≪≫ c ≪≫ q).toLinearEquiv.trans z

end SecondHomology

/-- The countably infinite free module in Theorem C, over the specified ring. -/
def homologyTwoEquiv : homology k 2 ≃ₗ[k] (ℕ →₀ k) :=
  (SecondHomology.homologyCyclesEquiv k).trans
    ((SecondHomology.cyclesEquiv k).trans (ReducedDifferential.kernelEquiv k))

end Parafree.TheoremC
