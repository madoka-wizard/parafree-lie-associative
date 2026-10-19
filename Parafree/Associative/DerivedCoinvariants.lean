import Parafree.Associative.Augmentation
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Actual left-derived coinvariants for modules over a noncommutative ring.
For an augmentation ideal I, the quotient functor M ↦ M / IM is the
coinvariant functor; its value derived at A/I is associative homology. -/
noncomputable section
namespace Parafree.Associative.DerivedCoinvariants
open CategoryTheory
universe u
variable {A : Type u} [Ring A] (I : Ideal A)

def relations (M : ModuleCat.{u} A) : Submodule A M := I • (⊤ : Submodule A M)

theorem map_relations {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    relations I M ≤ (relations I N).comap f.hom := by
  apply Submodule.smul_le.mpr
  intro r hr m _
  change f.hom (r • m) ∈ I • (⊤ : Submodule A N)
  rw [map_smul]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

def obj (M : ModuleCat.{u} A) : ModuleCat.{u} A := ModuleCat.of A (M ⧸ relations I M)

def map {M N : ModuleCat.{u} A} (f : M ⟶ N) : obj I M ⟶ obj I N :=
  ModuleCat.ofHom ((relations I M).mapQ (relations I N) f.hom (map_relations I f))

@[simp] theorem map_mk {M N : ModuleCat.{u} A} (f : M ⟶ N) (m : M) :
    map I f ((relations I M).mkQ m) = (relations I N).mkQ (f m) := rfl

def functor : ModuleCat.{u} A ⥤ ModuleCat.{u} A where
  obj := obj I
  map := map I
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m,rfl⟩ := (relations I M).mkQ_surjective x
    rfl
  map_comp {M N P} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m,rfl⟩ := (relations I M).mkQ_surjective x
    rfl

instance : (functor I).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m,rfl⟩ := (relations I M).mkQ_surjective x
    rfl

/-- Derived coinvariants of the trivial quotient module, not a presentation
quotient used as a substitute for homology. -/
def homology [I.IsTwoSided] (n : ℕ) : ModuleCat.{u} A :=
  ((functor I).leftDerived n).obj (ModuleCat.of A (A ⧸ I))

section Augmentation
variable {k : Type*} [CommRing k] [Algebra k A] (ε : A →ₐ[k] k)

/-- Coinvariants with their natural coefficient-ring module structure. -/
def coefficientFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} k :=
  functor (augmentationIdeal ε) ⋙ ModuleCat.restrictScalars (algebraMap k A)

instance : (coefficientFunctor ε).Additive := inferInstanceAs
  ((functor (augmentationIdeal ε)) ⋙ ModuleCat.restrictScalars (algebraMap k A)).Additive

/-- Tor with both trivial coefficient modules, as a module over the base ring. -/
def coefficientHomology (n : ℕ) : ModuleCat.{u} k :=
  ((coefficientFunctor ε).leftDerived n).obj (ModuleCat.of A (A ⧸ augmentationIdeal ε))

/-- The trivial quotient is the coefficient ring, with the augmentation action. -/
def trivialQuotientEquiv : (A ⧸ augmentationIdeal ε) ≃ₐ[k] k :=
  Ideal.quotientKerAlgEquivOfRightInverse
    (show Function.RightInverse (algebraMap k A) ε from fun r => by simp)

@[simp] theorem trivialQuotientEquiv_mk (a : A) :
    trivialQuotientEquiv ε ((augmentationIdeal ε).mkQ a) = ε a := rfl

theorem trivialQuotientEquiv_smul (a : A) (x : A ⧸ augmentationIdeal ε) :
    trivialQuotientEquiv ε (a • x) = ε a * trivialQuotientEquiv ε x := by
  obtain ⟨b,rfl⟩ := (augmentationIdeal ε).mkQ_surjective x
  change ε (a*b) = ε a * ε b
  exact map_mul _ _ _
end Augmentation

end Parafree.Associative.DerivedCoinvariants
