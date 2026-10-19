import Parafree.Associative.FilteredPBW

/-!
# Relative PBW with an adapted basis

The multiplication map from finitely supported families of enveloping
coefficients is an equivalence when the subalgebra basis is the initial block
of an ambient basis. The construction retains its left multiplication formula.
-/

noncomputable section

namespace Parafree.Associative.RelativePBW

open Module LieRings LieRings.PBW

variable {R J L ι κ : Type*} [CommRing R]
  [LieRing J] [LieAlgebra R J] [LieRing L] [LieAlgebra R L]
  [LinearOrder ι] [LinearOrder κ]

/-- Join the exponent vectors, with the first block ordered before the second. -/
def exponents : ((κ →₀ ℕ) × (ι →₀ ℕ)) ≃ ((ι ⊕ₗ κ) →₀ ℕ) :=
  (Equiv.prodComm _ _).trans Finsupp.sumFinsuppEquivProdFinsupp.symm

theorem sorted_exponents (q : κ →₀ ℕ) (p : ι →₀ ℕ) :
    ((exponents (q, p)).toMultiset.sort (· ≤ ·)) =
      (p.toMultiset.sort (· ≤ ·)).map (toLex ∘ Sum.inl) ++
        (q.toMultiset.sort (· ≤ ·)).map (toLex ∘ Sum.inr) := by
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Multiset.pairwise_sort _ _) ?_ ?_

  · apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact (Multiset.pairwise_sort p.toMultiset (· ≤ ·)).map (toLex ∘ Sum.inl)
        (fun _ _ h => Sum.Lex.inl_le_inl_iff.mpr h)
    · exact (Multiset.pairwise_sort q.toMultiset (· ≤ ·)).map (toLex ∘ Sum.inr)
        (fun _ _ h => Sum.Lex.inr_le_inr_iff.mpr h)
    · intro a ha b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
      exact Sum.Lex.inl_le_inr a b

  · apply Multiset.coe_eq_coe.mp
    rw [Multiset.sort_eq, ← Multiset.coe_add, ← Multiset.map_coe, ← Multiset.map_coe,
      Multiset.sort_eq, Multiset.sort_eq, Finsupp.toMultiset_map,
      Finsupp.toMultiset_map, ← map_add]
    congr 1
    exact Finsupp.sumElim_eq_add p q

/-- The actual ordered monomials, as a basis rather than a spanning family. -/
def basis (b : Basis ι R J) : Basis (ι →₀ ℕ) R (UEA R J) :=
  (MvPolynomial.basisMonomials ι R).map (FilteredPBW.equiv b)

@[simp] theorem basis_apply (b : Basis ι R J) (p : ι →₀ ℕ) :
    basis b p = orderedMonomial R J ι b p := by
  simp [basis, FilteredPBW.equiv, MvPolynomial.coe_basisMonomials]

variable (f : J →ₗ⁅R⁆ L) (b : Basis ι R J) (B : Basis (ι ⊕ₗ κ) R L)

/-- The canonical map of enveloping algebras. -/
def inclusion : UEA R J →ₐ[R] UEA R L :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp f)

@[simp] theorem inclusion_iota (x : J) :
    inclusion f (UniversalEnvelopingAlgebra.ι R x) = UniversalEnvelopingAlgebra.ι R (f x) :=
  UniversalEnvelopingAlgebra.lift_ι_apply R _ x

/-- Ordered products of the complementary basis block. -/
def complement (q : κ →₀ ℕ) : UEA R L :=
  ((q.toMultiset.sort (· ≤ ·)).map
    (fun i => UniversalEnvelopingAlgebra.ι R (B (toLex (Sum.inr i))))).prod

/-- The relative PBW equivalence, initially as an equivalence of base modules. -/
def equiv : ((κ →₀ ℕ) →₀ UEA R J) ≃ₗ[R] UEA R L :=
  (Finsupp.basis (fun _ : κ →₀ ℕ => basis b)).equiv (basis B)
    ((Equiv.sigmaEquivProd _ _).trans exponents)

theorem ordered_factor (hB : ∀ i, B (toLex (Sum.inl i)) = f (b i))
    (q : κ →₀ ℕ) (p : ι →₀ ℕ) :
    orderedMonomial R L (ι ⊕ₗ κ) B (exponents (q, p)) =
      inclusion f (orderedMonomial R J ι b p) * complement B q := by
  simp only [orderedMonomial, sorted_exponents, List.map_append, List.prod_append,
    List.map_map, Function.comp_def, hB, complement]
  congr 1
  simp only [map_list_prod, List.map_map, Function.comp_def, inclusion_iota]

theorem equiv_single (hB : ∀ i, B (toLex (Sum.inl i)) = f (b i))
    (q : κ →₀ ℕ) (a : UEA R J) :
    equiv b B (Finsupp.single q a) = inclusion f a * complement B q := by
  have h : (equiv b B).toLinearMap.comp (Finsupp.lsingle q) =
      (LinearMap.mulRight R (complement B q)).comp (inclusion f).toLinearMap := by
    apply (basis b).ext
    intro p
    change equiv b B (Finsupp.single q (basis b p)) = _
    have hp := Basis.equiv_apply
      (Finsupp.basis (fun _ : κ →₀ ℕ => basis b)) ⟨q, p⟩ (basis B)
      ((Equiv.sigmaEquivProd _ _).trans exponents)
    simpa only [Finsupp.coe_basis, basis_apply, Equiv.trans_apply,
      Equiv.sigmaEquivProd_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
      AlgHom.toLinearMap_apply, ordered_factor f b B hB] using hp
  exact LinearMap.congr_fun h a

end Parafree.Associative.RelativePBW
