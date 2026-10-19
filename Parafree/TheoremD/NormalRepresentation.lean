import Parafree.TheoremD.NormalWords
import Parafree.TheoremC.Presentation
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! The explicit left representation on irreducible words of the extended
presentation. It replaces an appeal to an external diamond lemma. -/
noncomputable section
namespace Parafree.TheoremD.NormalRepresentation
open Parafree.TheoremC
open Parafree.Associative NormalWords
variable (k : Type*) [CommRing k]

abbrev Space := BasisWord →₀ k
def basis (w : BasisWord) : Space k := Finsupp.single w 1

def prepend (i : Letter) (hi : i ≠ Y 0) (w : BasisWord) : BasisWord :=
  ⟨i :: w.val, normal_prepend hi w.property⟩

def prependOp (i : Letter) (hi : i ≠ Y 0) : Module.End k (Space k) :=
  Finsupp.lmapDomain k k (prepend i hi)

@[simp] theorem prependOp_basis (i : Letter) (hi : i ≠ Y 0) (w : BasisWord) :
    prependOp k i hi (basis k w) = basis k (prepend i hi w) := by
  simp [prependOp, basis]

def repeatPrepend (i : Letter) (hi : i ≠ Y 0) (n : ℕ) (w : BasisWord) : BasisWord :=
  ⟨List.replicate n i ++ w.val,
    normal_append (by intro j hj; exact (List.mem_replicate.mp hj).2 ▸ hi) w.property⟩

theorem prependOp_pow_basis (i : Letter) (hi : i ≠ Y 0) (n : ℕ) (w : BasisWord) :
    ((prependOp k i hi)^n) (basis k w) = basis k (repeatPrepend i hi n w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, prependOp_basis]
    rfl

def replaced (n : ℕ) (w : BasisWord) : BasisWord :=
  ⟨replacement n ++ w.val, normal_replacement n w.property⟩

def extra (n : ℕ) (w : BasisWord) : Space k :=
  if n < 2 then 0 else basis k (prepend (Z (n-2)) (by simp) w)

def leadingBasis (w : BasisWord) : Space k :=
  match h : parse w.val with
  | none => basis k ⟨Y 0 :: w.val, ⟨w.property, fun _ => h⟩⟩
  | some (n,t) =>
      let w' : BasisWord := ⟨t, normal_parse_suffix w.property h⟩
      basis k (replaced n w') + extra k n w'

def leading : Module.End k (Space k) := Finsupp.linearCombination k (leadingBasis k)

@[simp] theorem leading_basis (w : BasisWord) : leading k (basis k w) = leadingBasis k w := by
  simp [leading, basis]

theorem leading_basis_unparsed (w : BasisWord) (h : parse w.val = none) :
    leading k (basis k w) = basis k ⟨Y 0 :: w.val, ⟨w.property, fun _ => h⟩⟩ := by
  rw [leading_basis]
  unfold leadingBasis
  split
  · rfl
  · rename_i n t hp
    have he := h.symm.trans hp
    cases he

theorem leading_basis_block (n : ℕ) (w : BasisWord) :
    leading k (basis k (repeatPrepend (Y 1) (by decide) n (prepend (Y 2) (by decide) w))) =
      basis k (replaced n w) + extra k n w := by
  rw [leading_basis]
  unfold leadingBasis
  split
  · rename_i hp
    have he := (parse_block n w.val).symm.trans hp
    cases he
  · rename_i m t hp
    have he := Option.some.inj ((parse_block n w.val).symm.trans hp)
    have hn := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    dsimp at hn ht
    subst m
    subst t
    rfl

def yOp : Fin 6 → Module.End k (Space k) :=
  ![leading k, prependOp k (Y 1) (by decide), prependOp k (Y 2) (by decide),
    prependOp k (Y 3) (by decide), prependOp k (Y 4) (by decide), prependOp k (Y 5) (by decide)]

def zOp (n : ℕ) : Module.End k (Space k) := prependOp k (Z n) (by simp)

theorem left_block_basis (n : ℕ) (w : BasisWord) :
    (yOp k 0 * yOp k 1 ^ n * yOp k 2) (basis k w) =
      basis k (replaced n w) + extra k n w := by
  change leading k (((prependOp k (Y 1) (by decide))^n)
    (prependOp k (Y 2) (by decide) (basis k w))) = _
  rw [prependOp_basis, prependOp_pow_basis, leading_basis_block]

theorem right_block_basis (n : ℕ) (w : BasisWord) :
    (yOp k 3 * yOp k 4 ^ n * yOp k 5) (basis k w) = basis k (replaced n w) := by
  change prependOp k (Y 3) (by decide) (((prependOp k (Y 4) (by decide))^n)
    (prependOp k (Y 5) (by decide) (basis k w))) = _
  rw [prependOp_basis, prependOp_pow_basis, prependOp_basis]
  apply congrArg (basis k)
  apply Subtype.ext
  simp [prepend, repeatPrepend, replaced, replacement, List.append_assoc]

theorem operator_relations (n : ℕ) :
    yOp k 0 * yOp k 1 ^ n * yOp k 2 - yOp k 3 * yOp k 4 ^ n * yOp k 5 =
      if n < 2 then 0 else zOp k (n-2) := by
  apply (Finsupp.basisSingleOne : Module.Basis BasisWord k (Space k)).ext
  intro w
  change (yOp k 0 * yOp k 1 ^ n * yOp k 2) (basis k w) -
    (yOp k 3 * yOp k 4 ^ n * yOp k 5) (basis k w) = _
  rw [left_block_basis, right_block_basis, add_sub_cancel_left]
  by_cases hn : n < 2
  · simp [extra, hn]
  · simp [extra, hn, zOp, prependOp, basis]

def onFree : Free k →ₐ[k] Module.End k (Space k) :=
  FreeAlgebra.lift k (fun i => yOp k i - 1)

@[simp] theorem onFree_letter (i : Fin 6) : onFree k (letter k i) = yOp k i - 1 :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem onFree_shifted (i : Fin 6) : onFree k (1+letter k i) = yOp k i := by
  rw [map_add, map_one]
  rw [onFree_letter]
  simp

theorem onFree_relator (n : ℕ) : onFree k (relator k n) = if n < 2 then 0 else zOp k (n-2) := by
  simpa only [relator, map_sub, map_mul, map_pow, onFree_shifted] using operator_relations k n

def hom : A₀ k →ₐ[k] Module.End k (Space k) := quotientLift _ (onFree k)
  (twoSidedSpan_le (by
    rintro _ ⟨i,rfl⟩
    change onFree k (relator k i) = 0
    rw [onFree_relator, if_pos i.isLt]))

@[simp] theorem hom_shifted (i : Fin 6) : hom k (1+generator₀ k i) = yOp k i := by
  change hom k (1+toInitial k (letter k i)) = _
  rw [← map_one (toInitial k), ← map_add]
  exact onFree_shifted k i

@[simp] theorem hom_higher_relator (n : ℕ) : hom k (toInitial k (relator k (n+2))) = zOp k n := by
  change onFree k (relator k (n+2)) = zOp k n
  rw [onFree_relator, if_neg (by omega), Nat.add_sub_cancel]

end Parafree.TheoremD.NormalRepresentation
