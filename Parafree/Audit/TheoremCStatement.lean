import Parafree.TheoremC.Complete

/-! Literal statement checks over a nonzero commutative ring, without a
field, domain, Noetherian, or characteristic hypothesis. -/
noncomputable section
open Parafree.TheoremC Parafree.Associative CategoryTheory
variable (k : Type*) [CommRing k] [Nontrivial k]

example (n : ℕ) : relator k n =
    (1+FreeAlgebra.ι k (0 : Fin 6)) * (1+FreeAlgebra.ι k (1 : Fin 6))^n *
      (1+FreeAlgebra.ι k (2 : Fin 6)) -
    (1+FreeAlgebra.ι k (3 : Fin 6)) * (1+FreeAlgebra.ι k (4 : Fin 6))^n *
      (1+FreeAlgebra.ι k (5 : Fin 6)) := rfl
example : A k = (FreeAlgebra k (Fin 6) ⧸ twoSidedSpan (Set.range (relator k))) := rfl
example (i : Fin 6) : augmentation k (generator k i) = 0 := augmentation_generator k i
example (i : Fin 4) : fourToFull k (FreeAlgebra.ι k i) =
    generator k i.castSucc.castSucc := by
  change projection k (fourToInitial k (FreeAlgebra.ι k i)) = _
  rw [fourToInitial, FreeAlgebra.lift_ι_apply]
  rfl
example : (⨅ n : ℕ, (RingHom.ker (augmentation k)) ^ n) = ⊥ := theoremC k |>.1
example (n : ℕ) : Function.Bijective ((augmentedFourToFull k).quotientMap n) :=
  theoremC k |>.2.1 n

-- The standard left-derived coinvariant functor, with its base-ring action.
example (n : ℕ) : homology k n =
    (((DerivedCoinvariants.functor (RingHom.ker (augmentation k))) ⋙
      ModuleCat.restrictScalars (algebraMap k (A k))).leftDerived n).obj
      (ModuleCat.of (A k) (A k ⧸ RingHom.ker (augmentation k))) := rfl
example : Nonempty ((A k ⧸ RingHom.ker (augmentation k)) ≃ₐ[k] k) :=
  ⟨DerivedCoinvariants.trivialQuotientEquiv (augmentation k)⟩
example (a : A k) (x : A k ⧸ RingHom.ker (augmentation k)) :
    DerivedCoinvariants.trivialQuotientEquiv (augmentation k) (a • x) =
      augmentation k a * DerivedCoinvariants.trivialQuotientEquiv (augmentation k) x :=
  DerivedCoinvariants.trivialQuotientEquiv_smul _ _ _
example : Nonempty (homology k 2 ≃ₗ[k] (ℕ →₀ k)) := theoremC k |>.2.2.1
example : Function.Surjective (toFull k) := theoremC k |>.2.2.2.1
example : ¬ IsFinitelyPresented k (A k) := theoremC k |>.2.2.2.2
example : IsFinitelyPresented k (A k) ↔
    ∃ (n : ℕ) (f : FreeAlgebra k (Fin n) →ₐ[k] A k), Function.Surjective f ∧
      ∃ s : Finset (FreeAlgebra k (Fin n)), RingHom.ker f = twoSidedSpan (s : Set _) := Iff.rfl
