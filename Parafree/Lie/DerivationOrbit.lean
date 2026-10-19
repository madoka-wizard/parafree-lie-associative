import Mathlib.Algebra.Lie.Derivation.Basic

/-! Commutativity of a derivation orbit from three finite relations.
This is the integral algebraic step behind the solvable presentation in
Theorem B; it also applies in characteristic five. -/

namespace Parafree.Lie.DerivationOrbit

variable {L : Type*} [LieRing L]

/-- Successive applications of a derivation, with a transparent recursion. -/
def orbit (D : LieDerivation ℤ L L) (m : L) : ℕ → L
  | 0 => m
  | n + 1 => D (orbit D m n)

@[simp] theorem orbit_zero (D : LieDerivation ℤ L L) (m : L) : orbit D m 0 = m := rfl
@[simp] theorem orbit_succ (D : LieDerivation ℤ L L) (m : L) (n : ℕ) :
    orbit D m (n + 1) = D (orbit D m n) := rfl

variable (D E : LieDerivation ℤ L L) (m : L)
variable (hcomm : ∀ z, E (D z) = D (E z))
variable (hrel : (2 : ℤ) • E m = (-3 : ℤ) • D (D m))

include hcomm hrel in
theorem action (n : ℕ) : (2 : ℤ) • E (orbit D m n) = (-3 : ℤ) • orbit D m (n + 2) := by
  induction n with
  | zero => exact hrel
  | succ n ih =>
    change (2 : ℤ) • E (D (orbit D m n)) = (-3 : ℤ) • D (orbit D m (n + 2))
    rw [hcomm, ← map_smul, ih, map_smul]

include hcomm hrel in
/-- A simultaneous shift of both indices is controlled by two derivations. -/
theorem simultaneous_shift (i j : ℕ) :
    (6 : ℤ) • ⁅orbit D m (i + 1), orbit D m (j + 1)⁆ =
      (3 : ℤ) • D (D ⁅orbit D m i, orbit D m j⁆) +
        (2 : ℤ) • E ⁅orbit D m i, orbit D m j⁆ := by
  have he : (2 : ℤ) • E ⁅orbit D m i, orbit D m j⁆ =
      (-3 : ℤ) • ⁅orbit D m i, orbit D m (j + 2)⁆ +
      (-3 : ℤ) • ⁅orbit D m (i + 2), orbit D m j⁆ := by
    rw [LieDerivation.apply_lie_eq_add, smul_add, ← lie_smul, ← smul_lie,
      action D E m hcomm hrel, action D E m hcomm hrel, lie_smul, smul_lie]
  rw [he]
  simp only [LieDerivation.apply_lie_eq_add, map_add, orbit_succ]
  module

variable (h6 : Function.Injective (fun z : L => (6 : ℤ) • z))
variable (hbase : ⁅m, D m⁆ = 0)

include hcomm hrel h6 hbase in
theorem adjacent (i : ℕ) : ⁅orbit D m i, orbit D m (i + 1)⁆ = 0 := by
  induction i with
  | zero => exact hbase
  | succ i ih =>
    apply h6
    change (6 : ℤ) • ⁅orbit D m (i + 1), orbit D m (i + 1 + 1)⁆ = (6 : ℤ) • (0 : L)
    rw [simultaneous_shift D E m hcomm hrel, ih]
    simp only [map_zero, smul_zero, zero_add]

include hcomm hrel h6 hbase in
theorem forward (n i : ℕ) : ⁅orbit D m i, orbit D m (i + n)⁆ = 0 := by
  induction n using Nat.twoStepInduction generalizing i with
  | zero => simp only [Nat.add_zero, lie_self]
  | one => exact adjacent D E m hcomm hrel h6 hbase i
  | more n hn hn1 =>
    have he := congrArg D (hn1 i)
    rw [map_zero, LieDerivation.apply_lie_eq_add] at he
    have hi : ⁅D (orbit D m i), orbit D m (i + (n + 1))⁆ = 0 := by
      simpa only [orbit_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn (i + 1)
    rw [hi, add_zero] at he
    exact he

include hcomm hrel h6 hbase in
/-- Every pair of orbit elements commutes; no freeness or finiteness is assumed. -/
theorem pairwise_commute (i j : ℕ) : ⁅orbit D m i, orbit D m j⁆ = 0 := by
  rcases le_total i j with hij | hji
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact forward D E m hcomm hrel h6 hbase n i
  · rw [← lie_skew]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hji
    rw [forward D E m hcomm hrel h6 hbase n j, neg_zero]

/-- A derivation which raises weights by one gives the expected weight on every
iterate. This statement also works when different integral weights agree in
the coefficient ring. -/
theorem weight (T : LieDerivation ℤ L L) (k : ℤ)
    (hraise : ∀ z, T (D z) = D (T z) + D z) (hm : T m = k • m) (n : ℕ) :
    T (orbit D m n) = ((n : ℤ) + k) • orbit D m n := by
  induction n with
  | zero => simpa only [orbit_zero, Nat.cast_zero, zero_add] using hm
  | succ n ih =>
    change T (D (orbit D m n)) = ((↑(n + 1) : ℤ) + k) • D (orbit D m n)
    rw [hraise, ih, map_smul]
    simp only [Nat.cast_add, Nat.cast_one]
    module

end Parafree.Lie.DerivationOrbit
