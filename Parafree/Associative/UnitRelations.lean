import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Propagating the two relations in Theorem D

The argument is multiplicative and works in an arbitrary monoid. Its application uses
units of the form one plus an augmentation element in a nilpotent quotient.
-/

namespace Parafree.Associative

variable {M : Type*} [Monoid M]

/-- An intertwining relation propagates to all natural powers. -/
theorem pow_intertwine (x g y : M) (h : x * g = g * y) (n : ℕ) :
    x ^ n * g = g * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      x ^ (n + 1) * g = x ^ n * (x * g) := by rw [pow_succ, mul_assoc]
      _ = x ^ n * (g * y) := by rw [h]
      _ = (x ^ n * g) * y := (mul_assoc _ _ _).symm
      _ = (g * y ^ n) * y := by rw [ih]
      _ = g * y ^ (n + 1) := by rw [pow_succ, mul_assoc]

/-- The first two relations imply every higher relation when the three outer letters
are units. No commutativity hypothesis is used. -/
theorem relations_of_units (a d f : Mˣ) (b c e : M)
    (h₀ : (a : M) * c = (d : M) * (f : M))
    (h₁ : (a : M) * b * c = (d : M) * e * (f : M)) (n : ℕ) :
    (a : M) * b ^ n * c = (d : M) * e ^ n * (f : M) := by
  let g : M := (↑(a⁻¹) : M) * (d : M)
  have hc : c = g * (f : M) := by
    have h := congrArg (fun x : M => (↑(a⁻¹) : M) * x) h₀
    simpa [g, mul_assoc] using h
  have hag : (a : M) * g = (d : M) := by simp [g, ← mul_assoc]
  have hbg : b * g = g * e := by
    have h := congrArg (fun x : M => (↑(a⁻¹) : M) * x * (↑(f⁻¹) : M)) h₁
    simpa [hc, g, mul_assoc] using h
  calc
    (a : M) * b ^ n * c = (a : M) * (b ^ n * g) * (f : M) := by
      rw [hc]
      simp only [mul_assoc]
    _ = (a : M) * (g * e ^ n) * (f : M) := by rw [pow_intertwine b g e hbg]
    _ = (d : M) * e ^ n * (f : M) := by rw [← mul_assoc (a : M) g, hag]

/-- The same propagation lemma stated without choosing unit representatives. -/
theorem relations_of_isUnit (a b c d e f : M)
    (ha : IsUnit a) (hd : IsUnit d) (hf : IsUnit f)
    (h₀ : a * c = d * f) (h₁ : a * b * c = d * e * f) (n : ℕ) :
    a * b ^ n * c = d * e ^ n * f := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hd
  obtain ⟨f, rfl⟩ := hf
  exact relations_of_units a d f b c e h₀ h₁ n

section Ring

variable {A : Type*} [Ring A]

/-- The exact form needed in finite augmentation quotients of Theorem D. -/
theorem relations_of_nilpotent (a b c d x y : A)
    (ha : IsNilpotent a) (hd : IsNilpotent d) (hy : IsNilpotent y)
    (h₀ : (1 + a) * (1 + c) = (1 + d) * (1 + y))
    (h₁ : (1 + a) * (1 + b) * (1 + c) = (1 + d) * (1 + x) * (1 + y))
    (n : ℕ) :
    (1 + a) * (1 + b) ^ n * (1 + c) = (1 + d) * (1 + x) ^ n * (1 + y) :=
  relations_of_isUnit _ _ _ _ _ _ ha.isUnit_one_add hd.isUnit_one_add hy.isUnit_one_add
    h₀ h₁ n

end Ring

end Parafree.Associative
