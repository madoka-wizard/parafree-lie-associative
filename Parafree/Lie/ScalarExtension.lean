import Mathlib.Algebra.Lie.BaseChange

/-! Extension of a Lie homomorphism into an algebra over the larger scalar ring. -/

noncomputable section

namespace Parafree.Lie.ScalarExtension

open scoped TensorProduct

/-- Multiplication by an integer is cancellable in any module over a ring
where that integer has an inverse. -/
theorem int_smul_injective_of_mul_eq_one (S : Type*) [CommRing S]
    (n : ℤ) (b : S) (hb : (n : S) * b = 1)
    (M : Type*) [AddCommGroup M] [Module S M] :
    Function.Injective (fun x : M => n • x) := by
  intro x y h
  have h' : (n : S) • x = (n : S) • y := by
    simpa only [Int.cast_smul_eq_zsmul] using h
  have hh := congrArg (fun z => b • z) h'
  simpa only [smul_smul, mul_comm b (n : S), hb, one_smul] using hh

theorem int_two_smul_half (S : Type*) [CommRing S] (b : S)
    (hb : (2 : S) * b = 1) {M : Type*} [AddCommGroup M] [Module S M] (x : M) :
    (2 : ℤ) • (b • x) = x := by
  have h : (2 : ℤ) • (b • x) = (2 : S) • (b • x) := by simp only [two_smul]
  rw [h, smul_smul, hb, one_smul]

theorem int_two_smul_injective (S : Type*) [CommRing S] (b : S)
    (hb : (2 : S) * b = 1) (M : Type*) [AddCommGroup M] [Module S M] :
    Function.Injective (fun x : M => (2 : ℤ) • x) := by
  intro x y h
  have h' : (2 : S) • x = (2 : S) • y := by simpa only [two_smul] using h
  have := congrArg (fun t => b • t) h'
  simpa only [smul_smul, mul_comm b 2, hb, one_smul] using this

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
variable {L K : Type*} [LieRing L] [LieAlgebra R L]
  [LieRing K] [LieAlgebra R K] [LieAlgebra S K] [IsScalarTower R S K]

def linearLift (f : L →ₗ⁅R⁆ K) : S ⊗[R] L →ₗ[S] K :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : S →ₗ[S] S).smulRight f.toLinearMap)

@[simp] theorem linearLift_tmul (f : L →ₗ⁅R⁆ K) (s : S) (x : L) :
    linearLift S f (s ⊗ₜ[R] x) = s • f x := rfl

theorem linearLift_lie (f : L →ₗ⁅R⁆ K) (x y : S ⊗[R] L) :
    linearLift S f ⁅x, y⁆ = ⁅linearLift S f x, linearLift S f y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_lie, map_zero]
  | add a b ha hb => simp only [add_lie, map_add, ha, hb]
  | tmul s x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [lie_zero, map_zero]
    | add a b ha hb => simp only [lie_add, map_add, ha, hb]
    | tmul t y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, linearLift_tmul,
        LieHom.map_lie, smul_lie, lie_smul, smul_smul, mul_comm]

def lift (f : L →ₗ⁅R⁆ K) : S ⊗[R] L →ₗ⁅S⁆ K where
  __ := linearLift S f
  map_lie' := linearLift_lie S f _ _

@[simp] theorem lift_tmul (f : L →ₗ⁅R⁆ K) (s : S) (x : L) :
    lift S f (s ⊗ₜ[R] x) = s • f x := rfl

end Parafree.Lie.ScalarExtension
