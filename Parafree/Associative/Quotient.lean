import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! Algebra maps out of noncommutative two-sided ideal quotients. -/
noncomputable section
namespace Parafree.Associative
variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]

abbrev twoSidedSpan (s : Set A) : Ideal A := (TwoSidedIdeal.span s).asIdeal

instance twoSidedSpan_isTwoSided (s : Set A) : (twoSidedSpan s).IsTwoSided := inferInstance

theorem subset_twoSidedSpan {s : Set A} {a : A} (ha : a ∈ s) : a ∈ twoSidedSpan s :=
  TwoSidedIdeal.subset_span ha

theorem twoSidedSpan_le {s : Set A} {I : Ideal A} [I.IsTwoSided]
    (h : ∀ x ∈ s, x ∈ I) : twoSidedSpan s ≤ I := by
  intro x hx
  have hle : TwoSidedIdeal.span s ≤ I.toTwoSided :=
    TwoSidedIdeal.span_le.mpr (fun x hx => Ideal.mem_toTwoSided.mpr (h x hx))
  exact Ideal.mem_toTwoSided.mp (hle hx)

def quotientLift (I : Ideal A) [I.IsTwoSided] (f : A →ₐ[R] B)
    (h : I ≤ RingHom.ker f) : A ⧸ I →ₐ[R] B where
  __ := Ideal.Quotient.lift I f.toRingHom h
  commutes' r := f.commutes r

@[simp] theorem quotientLift_mk (I : Ideal A) [I.IsTwoSided] (f : A →ₐ[R] B)
    (h : I ≤ RingHom.ker f) (a : A) :
    quotientLift I f h (Ideal.Quotient.mkₐ R I a) = f a := rfl

theorem quotientLift_surjective (I : Ideal A) [I.IsTwoSided] (f : A →ₐ[R] B)
    (h : I ≤ RingHom.ker f) (hf : Function.Surjective f) :
    Function.Surjective (quotientLift I f h) := by
  intro b
  obtain ⟨a,rfl⟩ := hf b
  exact ⟨Ideal.Quotient.mkₐ R I a,rfl⟩

/-- Membership in an ideal power is preserved by any ring homomorphism
that maps the original ideals into one another. -/
theorem map_mem_idealPower (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : ∀ x ∈ I, f x ∈ J) (n : ℕ) {x : A} (hx : x ∈ I ^ n) : f x ∈ J ^ n := by
  induction n generalizing x with
  | zero => simpa only [Submodule.pow_zero, Ideal.one_eq_top] using (Submodule.mem_top : f x ∈ (⊤ : Ideal B))
  | succ n ih =>
    rw [Submodule.pow_succ] at hx ⊢
    exact Submodule.mul_induction_on hx
      (fun a ha b hb => by rw [map_mul]; exact Ideal.mul_mem_mul (ih ha) (h b hb))
      (fun a b ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)

end Parafree.Associative
