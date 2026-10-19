import Parafree.Lie.HomologicalComparison

/-! The natural maps on the layers of the lower central series. -/

noncomputable section
namespace Parafree.Lie

variable (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]

/-- The next lower-central term as a submodule of the current term. -/
abbrev layerRelations (n : ℕ) : Submodule R (lowerCentral R L n) :=
  (lowerCentral R L (n + 1)).toSubmodule.comap (lowerCentral R L n).toSubmodule.subtype

abbrev LowerCentralLayer (n : ℕ) := lowerCentral R L n ⧸ layerRelations R L n

variable {R L} {M : Type*} [LieRing M] [LieAlgebra R M]

def lowerCentralRestriction (f : L →ₗ⁅R⁆ M) (n : ℕ) :
    lowerCentral R L n →ₗ[R] lowerCentral R M n :=
  f.toLinearMap.restrict (fun _ hx => map_mem_lowerCentral f n hx)

/-- The actual map on successive layers induced by the given Lie homomorphism. -/
def layerMap (f : L →ₗ⁅R⁆ M) (n : ℕ) :
    LowerCentralLayer R L n →ₗ[R] LowerCentralLayer R M n :=
  (layerRelations R L n).mapQ (layerRelations R M n) (lowerCentralRestriction f n)
    (fun _ hx => map_mem_lowerCentral f (n + 1) hx)

@[simp] theorem layerMap_mk (f : L →ₗ⁅R⁆ M) (n : ℕ) (x : lowerCentral R L n) :
    layerMap f n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (lowerCentralRestriction f n x) := rfl

/-- No choice of bases is involved in the comparison of the layers. -/
theorem layerMap_bijective (f : L →ₗ⁅R⁆ M) (n : ℕ)
    (hn : Function.Injective (nilpotentMap f n))
    (hn1 : Function.Bijective (nilpotentMap f (n + 1))) :
    Function.Bijective (layerMap f n) := by
  constructor
  · intro x y h
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (layerRelations R L n) x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (layerRelations R L n) y
    apply (Submodule.Quotient.eq _).mpr
    change (x : L) - (y : L) ∈ lowerCentral R L (n + 1)
    apply (nilpotentMap_injective_iff f (n + 1)).mp hn1.1
    have hd := (Submodule.Quotient.eq (layerRelations R M n)).mp h
    change f x - f y ∈ lowerCentral R M (n + 1) at hd
    simpa only [map_sub] using hd
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (layerRelations R M n) y
    obtain ⟨x, hx⟩ := (nilpotentMap_surjective_iff f (n + 1)).mp hn1.2 (y : M)
    have hfx : f x ∈ lowerCentral R M n := by
      have hd := LieModule.antitone_lowerCentralSeries R M M (Nat.le_succ n) hx
      have hh := (lowerCentral R M n).sub_mem y.property hd
      simpa only [sub_sub_cancel] using hh
    have hxL := (nilpotentMap_injective_iff f n).mp hn x hfx
    refine ⟨Submodule.Quotient.mk (⟨x, hxL⟩ : lowerCentral R L n), ?_⟩
    rw [layerMap_mk]
    apply (Submodule.Quotient.eq _).mpr
    change f x - (y : M) ∈ lowerCentral R M (n + 1)
    simpa only [neg_sub] using (lowerCentral R M (n + 1)).neg_mem hx

/-- Naturality on layers for a para-equivalence. -/
def IsParaEquivalence.layerEquiv {f : L →ₗ⁅R⁆ M} (h : IsParaEquivalence f) (n : ℕ) :
    LowerCentralLayer R L n ≃ₗ[R] LowerCentralLayer R M n :=
  LinearEquiv.ofBijective (layerMap f n) (layerMap_bijective f n (h n).1 (h (n + 1)))

end Parafree.Lie
