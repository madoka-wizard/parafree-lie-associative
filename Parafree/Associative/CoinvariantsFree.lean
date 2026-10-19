import Parafree.Associative.DerivedCoinvariants

/-! Coinvariants of a free module are the free module over the coefficient
ring, naturally with respect to maps of free modules. -/
noncomputable section
namespace Parafree.Associative.CoinvariantsFree
open CategoryTheory
universe u
variable {k A : Type u} [CommRing k] [Ring A] [Algebra k A]
variable (ε : A →ₐ[k] k) (ι : Type)

abbrev relations := DerivedCoinvariants.relations (augmentationIdeal ε)
  (ModuleCat.of A (ι →₀ A))

def reduce : (ι →₀ A) →ₗ[k] (ι →₀ k) := Finsupp.mapRange.linearMap ε.toLinearMap

def sectionMap : (ι →₀ k) →ₗ[k] (ι →₀ A) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap k A)

@[simp] theorem reduce_apply (v : ι →₀ A) (i : ι) : reduce ε ι v i = ε (v i) := rfl
@[simp] theorem reduce_single (i : ι) (a : A) :
    reduce ε ι (Finsupp.single i a) = Finsupp.single i (ε a) := by simp [reduce]

theorem reduce_smul (a : A) (v : ι →₀ A) : reduce ε ι (a • v) = ε a • reduce ε ι v := by
  ext i
  exact map_mul ε a (v i)

@[simp] theorem reduce_section (v : ι →₀ k) : reduce ε ι (sectionMap ι v) = v := by
  ext i
  change ε (algebraMap k A (v i)) = v i
  exact ε.commutes (v i)

theorem relations_le_ker : (relations ε ι).restrictScalars k ≤ LinearMap.ker (reduce ε ι) := by
  intro v hv
  change reduce ε ι v = 0
  change v ∈ augmentationIdeal ε • (⊤ : Submodule A (ι →₀ A)) at hv
  refine Submodule.smul_induction_on (p := fun w : ι →₀ A => reduce ε ι w = 0) hv ?_ ?_
  · intro a ha x _
    rw [reduce_smul, show ε a = 0 from ha, zero_smul]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

theorem single_mem_relations (i : ι) {a : A} (ha : ε a = 0) :
    Finsupp.single i a ∈ relations ε ι := by
  have he : Finsupp.single i a = a • (Finsupp.single i 1 : ι →₀ A) := by simp
  rw [he]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

theorem reduce_eq_zero_iff (v : ι →₀ A) : reduce ε ι v = 0 ↔ v ∈ relations ε ι := by
  constructor
  · intro hv
    have hi (i : ι) : ε (v i) = 0 := congrArg (fun w : ι →₀ k => w i) hv
    rw [← v.sum_single]
    apply Submodule.sum_mem
    intro i _
    exact single_mem_relations ε ι i (hi i)
  · exact fun hv => relations_le_ker ε ι hv

def quotientMap : (ι →₀ A) ⧸ relations ε ι →ₗ[k] (ι →₀ k) :=
  ((relations ε ι).restrictScalars k).liftQ (reduce ε ι) (relations_le_ker ε ι)

/-- The usual identification of free-module coinvariants with coefficient vectors. -/
def equiv : ((ι →₀ A) ⧸ relations ε ι) ≃ₗ[k] (ι →₀ k) :=
  LinearEquiv.ofBijective (quotientMap ε ι) (by
    constructor
    · intro x y h
      obtain ⟨v,rfl⟩ := (relations ε ι).mkQ_surjective x
      obtain ⟨w,rfl⟩ := (relations ε ι).mkQ_surjective y
      apply (Submodule.Quotient.eq _).mpr
      apply (reduce_eq_zero_iff ε ι _).mp
      rw [map_sub]
      exact sub_eq_zero.mpr h
    · intro v
      exact ⟨(relations ε ι).mkQ (sectionMap ι v),reduce_section ε ι v⟩)

@[simp] theorem equiv_mk (v : ι →₀ A) : equiv ε ι ((relations ε ι).mkQ v) = reduce ε ι v := rfl

end Parafree.Associative.CoinvariantsFree
