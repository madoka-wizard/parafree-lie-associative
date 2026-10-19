import Parafree.Homology.Coefficients.Acyclicity
import Mathlib.Algebra.Lie.DirectSum

/-!
# Coefficient homology and direct sums

Tensoring the exterior chain module commutes with arbitrary direct sums of
coefficient modules. Componentwise cycle fillings assemble into a finite sum,
so exactness is preserved without a finite-rank or flatness assumption.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.DirectSums

open CategoryTheory
open scoped TensorProduct DirectSum
open Parafree.Linear.ExteriorTensor (Chain)

universe u v w z
variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
variable {ι : Type z} (M : ι → Type w) [DecidableEq ι]
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, LieRingModule L (M i)] [∀ i, LieModule R L (M i)]

def chains (n : ℕ) : Chain R L (⨁ i, M i) n ≃ₗ[R] (⨁ i, Chain R L (M i) n) :=
  TensorProduct.directSumRight R R (⋀[R]^n L) M

omit [∀ i, LieModule R L (M i)] in
theorem chains_component (n : ℕ) (c : Chain R L (⨁ i, M i) n) (i : ι) :
    chains R L M n c i = chainMap (_root_.DirectSum.lieModuleComponent R ι L M i) n c := by
  induction c using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero, _root_.DirectSum.zero_apply, map_zero]
  | add a b ha hb => simp only [map_add, _root_.DirectSum.add_apply, ha, hb]
  | tmul u m =>
    simp only [chains, TensorProduct.directSumRight_tmul, chainMap_tmul]
    rfl

omit [∀ i, LieModule R L (M i)] in
theorem chains_inclusion (n : ℕ) (i : ι) (c : Chain R L (M i) n) :
    chains R L M n (chainMap (_root_.DirectSum.lieModuleOf R ι L M i) n c) =
      _root_.DirectSum.lof R ι (fun j => Chain R L (M j) n) i c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul u m =>
    change TensorProduct.directSumRight R R (⋀[R]^n L) M
      (u ⊗ₜ[R] _root_.DirectSum.lof R ι M i m) = _
    exact TensorProduct.directSumRight_tmul_lof R R u i m

open Classical in
omit [∀ i, LieModule R L (M i)] in
theorem decompose (n : ℕ) (c : Chain R L (⨁ i, M i) n) :
    (∑ i ∈ (chains R L M n c).support,
      chainMap (_root_.DirectSum.lieModuleOf R ι L M i) n (chains R L M n c i)) = c := by
  classical
  apply (chains R L M n).injective
  have hs : chains R L M n (∑ i ∈ (chains R L M n c).support,
      chainMap (_root_.DirectSum.lieModuleOf R ι L M i) n (chains R L M n c i)) =
      ∑ i ∈ (chains R L M n c).support, chains R L M n
        (chainMap (_root_.DirectSum.lieModuleOf R ι L M i) n (chains R L M n c i)) :=
    map_sum (chains R L M n).toLinearMap.toAddMonoidHom _ _
  rw [hs]
  simp only [chains_inclusion]
  exact _root_.DirectSum.sum_support_of (chains R L M n c)

/-- Finite-support assembly of fillings in an arbitrary direct sum of coefficients. -/
theorem fill (n : ℕ)
    (hfill : ∀ i, ∀ x : Chain R L (M i) (n + 1), differential R L (M i) n x = 0 →
      ∃ y, differential R L (M i) (n + 1) y = x)
    (x : Chain R L (⨁ i, M i) (n + 1))
    (hx : differential R L (⨁ i, M i) n x = 0) :
    ∃ y, differential R L (⨁ i, M i) (n + 1) y = x := by
  classical
  have hi (i : ι) : differential R L (M i) n (chains R L M (n + 1) x i) = 0 := by
    rw [chains_component, ← chainMap_differential_apply, hx, map_zero]
  choose y hy using fun i => hfill i (chains R L M (n + 1) x i) (hi i)
  refine ⟨∑ i ∈ (chains R L M (n + 1) x).support,
    chainMap (_root_.DirectSum.lieModuleOf R ι L M i) (n + 2) (y i), ?_⟩
  simp only [map_sum, ← chainMap_differential_apply, hy]
  exact decompose R L M (n + 1) x

theorem exactAt (n : ℕ) (hn : n ≠ 0)
    (hexact : ∀ i, (complex R L (M i)).ExactAt n) :
    (complex R L (⨁ i, M i)).ExactAt n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [exactAt_succ_iff_fill]
  exact fill R L M k (fun i => exactAt_succ_iff_fill k |>.mp (hexact i))

end Parafree.Homology.Coefficients.DirectSums
