import Parafree.Lie.Quotient
import Mathlib.Algebra.Lie.Nilpotent

/-!
The index `n` here denotes the manuscript's `gamma_(n+1)`.
Thus index zero is the whole algebra and index one is its derived ideal.
-/

namespace Parafree.Lie

variable (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]

abbrev lowerCentral (n : ℕ) : LieIdeal R L := LieModule.lowerCentralSeries R L L n

def residualIdeal : LieIdeal R L := ⨅ n, lowerCentral R L n

def ResiduallyNilpotent : Prop := residualIdeal R L = ⊥

variable {R L} {M : Type*} [LieRing M] [LieAlgebra R M]

theorem map_mem_lowerCentral (f : L →ₗ⁅R⁆ M) (n : ℕ) {x : L}
    (hx : x ∈ lowerCentral R L n) : f x ∈ lowerCentral R M n :=
  LieIdeal.map_lowerCentralSeries_le n (LieIdeal.mem_map hx)

def nilpotentMap (f : L →ₗ⁅R⁆ M) (n : ℕ) :
    L ⧸ lowerCentral R L n →ₗ⁅R⁆ M ⧸ lowerCentral R M n :=
  quotientMap _ _ f (fun _ hx => map_mem_lowerCentral f n hx)

@[simp] theorem nilpotentMap_mk (f : L →ₗ⁅R⁆ M) (n : ℕ) (x : L) :
    nilpotentMap f n (quotientMk _ x) = quotientMk _ (f x) := rfl

def IsParaEquivalence (f : L →ₗ⁅R⁆ M) : Prop :=
  ∀ n, Function.Bijective (nilpotentMap f n)

theorem lowerCentral_quotient_eq_bot (n : ℕ) :
    lowerCentral R (L ⧸ lowerCentral R L n) n = ⊥ := by
  change LieModule.lowerCentralSeries R _ _ n = ⊥
  rw [← LieIdeal.lowerCentralSeries_map_eq n (quotientMk_surjective (lowerCentral R L n)),
    LieIdeal.map_eq_bot_iff, quotientMk_ker]

theorem lowerCentral_le_ker (f : L →ₗ⁅R⁆ M) (n : ℕ)
    (h : lowerCentral R M n = ⊥) : lowerCentral R L n ≤ f.ker := by
  intro x hx
  have hm := map_mem_lowerCentral f n hx
  simpa only [h, LieSubmodule.mem_bot] using hm

theorem lie_eq_zero_of_lowerCentral_one (h : lowerCentral R L 1 = ⊥) (x y : L) :
    ⁅x, y⁆ = 0 := by
  have hmem : ⁅x, y⁆ ∈ lowerCentral R L 1 := by
    simp only [lowerCentral, LieModule.lowerCentralSeries_succ,
      LieModule.lowerCentralSeries_zero]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
  simpa only [h, LieSubmodule.mem_bot] using hmem

theorem residualIdeal_le (n : ℕ) : residualIdeal R L ≤ lowerCentral R L n :=
  iInf_le _ n

theorem mem_lowerCentral_quotient_iff (I : LieIdeal R L) (n : ℕ)
    (hI : I ≤ lowerCentral R L n) (x : L) :
    quotientMk I x ∈ lowerCentral R (L ⧸ I) n ↔ x ∈ lowerCentral R L n := by
  constructor
  · intro hx
    change quotientMk I x ∈ LieModule.lowerCentralSeries R _ _ n at hx
    rw [← LieIdeal.lowerCentralSeries_map_eq n (quotientMk_surjective I)] at hx
    obtain ⟨y, heq⟩ := LieIdeal.mem_map_of_surjective (quotientMk_surjective I) hx
    have hxy : x - (y : L) ∈ I := (quotientMk_eq_zero I _).mp (by
      rw [map_sub, heq, sub_self])
    have := (lowerCentral R L n).add_mem (hI hxy) y.property
    simpa using this
  · exact map_mem_lowerCentral (quotientMk I) n

theorem residualQuotient_residuallyNilpotent :
    ResiduallyNilpotent R (L ⧸ residualIdeal R L) := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨x, rfl⟩ := quotientMk_surjective (residualIdeal R L) x
  apply (quotientMk_eq_zero _ _).mpr
  change x ∈ ⨅ n, lowerCentral R L n
  rw [LieSubmodule.mem_iInf]
  intro n
  exact (mem_lowerCentral_quotient_iff _ n (residualIdeal_le n) x).mp
    ((iInf_le (lowerCentral R (L ⧸ residualIdeal R L)) n) hx)

theorem residualQuotient_isParaEquivalence :
    IsParaEquivalence (quotientMk (residualIdeal R L)) := by
  intro n
  constructor
  · intro x y h
    obtain ⟨x, rfl⟩ := quotientMk_surjective (lowerCentral R L n) x
    obtain ⟨y, rfl⟩ := quotientMk_surjective (lowerCentral R L n) y
    apply sub_eq_zero.mp
    rw [← map_sub, quotientMk_eq_zero]
    apply (mem_lowerCentral_quotient_iff _ n (residualIdeal_le n) (x - y)).mp
    apply (quotientMk_eq_zero _ _).mp
    rw [map_sub, map_sub]
    exact sub_eq_zero.mpr h
  · intro y
    obtain ⟨y, rfl⟩ := quotientMk_surjective _ y
    obtain ⟨y, rfl⟩ := quotientMk_surjective _ y
    exact ⟨quotientMk _ y, rfl⟩

theorem IsParaEquivalence.comp {N : Type*} [LieRing N] [LieAlgebra R N]
    {f : L →ₗ⁅R⁆ M} {g : M →ₗ⁅R⁆ N}
    (hg : IsParaEquivalence g) (hf : IsParaEquivalence f) :
    IsParaEquivalence (g.comp f) := by
  intro n
  have heq : nilpotentMap (g.comp f) n = (nilpotentMap g n).comp (nilpotentMap f n) := by
    apply quotient_hom_ext
    apply LieHom.ext
    intro x
    rfl
  rw [heq]
  exact (hg n).comp (hf n)

end Parafree.Lie
