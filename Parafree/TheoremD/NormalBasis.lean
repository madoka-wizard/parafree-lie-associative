import Parafree.TheoremD.NormalRepresentation

/-! The normal-word basis of the actual two-relator quotient. -/
noncomputable section
namespace Parafree.TheoremD.NormalBasis
open Parafree.TheoremC
open Parafree.Associative NormalWords NormalRepresentation
variable (k : Type*) [CommRing k]

def value : Letter → A₀ k
  | Sum.inl i => 1+generator₀ k i
  | Sum.inr n => toInitial k (relator k (n+2))

def wordValue (w : Word) : A₀ k := (w.map (value k)).prod
@[simp] theorem wordValue_nil : wordValue k [] = 1 := rfl
@[simp] theorem wordValue_cons (i : Letter) (w : Word) :
    wordValue k (i :: w) = value k i * wordValue k w := rfl
@[simp] theorem wordValue_append (v w : Word) : wordValue k (v ++ w) = wordValue k v * wordValue k w := by
  simp [wordValue, List.prod_append]
@[simp] theorem wordValue_replicate (i : Letter) (n : ℕ) :
    wordValue k (List.replicate n i) = value k i ^ n := by simp [wordValue]

def empty : BasisWord := ⟨[],trivial⟩

def represent : A₀ k →ₗ[k] Space k where
  toFun a := NormalRepresentation.hom k a (basis k empty)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def evaluate : Space k →ₗ[k] A₀ k := Finsupp.linearCombination k (fun w => wordValue k w.val)

@[simp] theorem evaluate_basis (w : BasisWord) : evaluate k (basis k w) = wordValue k w.val := by
  simp [evaluate, basis]

/-- A normal word acting on the empty word returns precisely its basis vector. -/
theorem represent_wordValue (w : Word) (hw : Normal w) :
    represent k (wordValue k w) = basis k ⟨w,hw⟩ := by
  induction w with
  | nil => simp [represent, empty]
  | cons i w ih =>
    have ht := hw.1
    have hrec := ih ht
    change NormalRepresentation.hom k (value k i * wordValue k w) (basis k empty) = _
    rw [map_mul, Module.End.mul_apply]
    change NormalRepresentation.hom k (value k i) (represent k (wordValue k w)) = _
    rw [hrec]
    cases i with
    | inl i =>
      change NormalRepresentation.hom k (1+generator₀ k i) _ = _
      rw [hom_shifted]
      fin_cases i
      · exact leading_basis_unparsed k ⟨w,ht⟩ (hw.2 rfl)
      all_goals exact prependOp_basis k _ _ ⟨w,ht⟩
    | inr n =>
      change NormalRepresentation.hom k (toInitial k (relator k (n+2))) _ = _
      rw [hom_higher_relator]
      exact prependOp_basis k _ _ ⟨w,ht⟩

theorem represent_evaluate : (represent k).comp (evaluate k) = LinearMap.id := by
  apply (Finsupp.basisSingleOne : Module.Basis BasisWord k (Space k)).ext
  intro w
  change represent k (evaluate k (basis k w)) = basis k w
  rw [evaluate_basis]
  exact represent_wordValue k w.val w.property

theorem evaluate_injective : Function.Injective (evaluate k) := by
  have h : Function.LeftInverse (represent k) (evaluate k) :=
    fun x => LinearMap.congr_fun (represent_evaluate k) x
  exact h.injective

theorem evaluate_prepend (i : Letter) (hi : i ≠ Y 0) (w : BasisWord) :
    evaluate k (prependOp k i hi (basis k w)) = value k i * wordValue k w.val := by
  rw [prependOp_basis, evaluate_basis]
  rfl

theorem evaluate_extra (n : ℕ) (w : BasisWord) :
    evaluate k (extra k n w) = toInitial k (relator k n) * wordValue k w.val := by
  cases n with
  | zero =>
    have hr : toInitial k (relator k 0) = 0 := initial_relator k (0 : Fin 2)
    simp [extra, hr]
  | succ n =>
    cases n with
    | zero =>
      have hr : toInitial k (relator k 1) = 0 := initial_relator k (1 : Fin 2)
      simp [extra, hr]
    | succ n =>
      simp only [extra, show ¬n+1+1 < 2 by omega, if_false,
        evaluate_basis, prepend, wordValue_cons, value]
      rw [show n+1+1-2+2 = n+1+1 by omega]

theorem evaluate_leading (w : BasisWord) :
    evaluate k (leading k (basis k w)) = value k (Y 0) * wordValue k w.val := by
  rw [leading_basis]
  unfold leadingBasis
  split
  · rw [evaluate_basis, wordValue_cons]
  · rename_i n t hp
    rw [map_add, evaluate_basis, evaluate_extra]
    change wordValue k (replacement n ++ t) + toInitial k (relator k n) * wordValue k t = _
    rw [wordValue_append, parse_spec hp]
    simp only [replacement, wordValue_cons, wordValue_append, wordValue_replicate,
      wordValue_nil, mul_one]
    have he : toInitial k (relator k n) =
        value k (Y 0) * value k (Y 1)^n * value k (Y 2) -
          value k (Y 3) * value k (Y 4)^n * value k (Y 5) := by
      simp [relator, value, generator₀]
    rw [he]
    simp only [sub_mul, mul_assoc]
    simp

theorem evaluate_yOp (i : Fin 6) :
    (evaluate k).comp (yOp k i) = (LinearMap.mulLeft k (value k (Y i))).comp (evaluate k) := by
  apply (Finsupp.basisSingleOne : Module.Basis BasisWord k (Space k)).ext
  intro w
  change evaluate k (yOp k i (basis k w)) = value k (Y i) * evaluate k (basis k w)
  rw [evaluate_basis]
  fin_cases i
  · exact evaluate_leading k w
  all_goals exact evaluate_prepend k _ _ w

theorem evaluate_onFree (a : Free k) (v : Space k) :
    evaluate k (NormalRepresentation.onFree k a v) = toInitial k a * evaluate k v := by
  induction a using FreeAlgebra.induction generalizing v with
  | grade0 r => simp [Algebra.smul_def]
  | grade1 i =>
    change evaluate k (NormalRepresentation.onFree k (letter k i) v) =
      generator₀ k i * evaluate k v
    rw [NormalRepresentation.onFree_letter, LinearMap.sub_apply, map_sub]
    have he := LinearMap.congr_fun (evaluate_yOp k i) v
    change evaluate k (yOp k i v) = (1+generator₀ k i) * evaluate k v at he
    rw [he, add_mul, one_mul]
    simp
  | mul a b iha ihb =>
    rw [map_mul, Module.End.mul_apply, iha, ihb, map_mul, mul_assoc]
  | add a b iha ihb =>
    rw [map_add, LinearMap.add_apply, map_add, iha, ihb, map_add, add_mul]

theorem evaluate_represent : (evaluate k).comp (represent k) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective k (initialIdeal k) x
  change evaluate k (NormalRepresentation.onFree k a (basis k empty)) = toInitial k a
  rw [evaluate_onFree, evaluate_basis]
  simp [empty]

/-- The irreducible words of the extended presentation form a basis of the
literal two-relator quotient, with explicit inverse coordinates. -/
def equiv : Space k ≃ₗ[k] A₀ k :=
  { evaluate k with
    invFun := represent k
    left_inv := fun x => LinearMap.congr_fun (represent_evaluate k) x
    right_inv := fun x => LinearMap.congr_fun (evaluate_represent k) x }

def wordBasis : Module.Basis BasisWord k (A₀ k) := Finsupp.basisSingleOne.map (equiv k)

@[simp] theorem wordBasis_apply (w : BasisWord) : wordBasis k w = wordValue k w.val := by
  change evaluate k (basis k w) = wordValue k w.val
  exact evaluate_basis k w

end Parafree.TheoremD.NormalBasis
