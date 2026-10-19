import Mathlib.Algebra.Lie.Derivation.Basic

/-! Integral derivation identities used by Theorem B.  They hold in every
Lie ring, before any localization or quotient is taken. -/

namespace Parafree.TheoremB

variable {L : Type*} [LieRing L]

def w (t a : L) : L := ⁅t, a⁆ - (2 : ℤ) • a

def f₁ (t a : L) : L := ⁅t, ⁅t, w t a⁆⁆ - w t a

def h (t a : L) : L := ⁅a, ⁅t, ⁅t, a⁆⁆⁆

def c (t a : L) : L := ⁅w t a, ⁅w t a, ⁅t, w t a⁆⁆⁆

def f₂ (t a : L) : L := h t a - c t a

/-- Left adjoint action as a derivation (the library's `inner` uses the
opposite convention). -/
def ad (t : L) : LieDerivation ℤ L L where
  toLinearMap := LieAlgebra.ad ℤ L t
  leibniz' a b := by
    change ⁅t, ⁅a, b⁆⁆ = ⁅a, ⁅t, b⁆⁆ - ⁅b, ⁅t, a⁆⁆
    rw [leibniz_lie, ← lie_skew b ⁅t, a⁆, sub_neg_eq_add]
    exact add_comm _ _

@[simp] theorem ad_apply (t x : L) : ad t x = ⁅t, x⁆ := rfl

/-- The quadratic part of the identity, for an arbitrary derivation. -/
theorem derivation_quadratic_identity (D : LieDerivation ℤ L L) (a : L) :
    let w := D a - (2 : ℤ) • a
    let f := D (D w) - w
    let h := ⁅a, D (D a)⁆
    D (D h) - (4 : ℤ) • D h + (3 : ℤ) • h = D ⁅a, f⁆ + ⁅w, f⁆ := by
  dsimp only
  simp only [map_add, map_sub, map_smul, LieDerivation.apply_lie_eq_add,
    lie_sub, sub_lie, lie_smul, smul_lie, lie_self, map_zero, smul_zero]
  module

/-- The cubic part; the only nonlinear cancellation is the Jacobi identity. -/
theorem derivation_cubic_identity (D : LieDerivation ℤ L L) (w : L) :
    let f := D (D w) - w
    let c := ⁅w, ⁅w, D w⁆⁆
    D (D c) - c = (3 : ℤ) • ⁅D w, ⁅w, f⁆⁆ + ⁅w, ⁅w, D f⁆⁆ := by
  dsimp only
  have hJ := leibniz_lie (D (D w)) w (D w)
  simp only [← lie_skew (D (D w)) w, ← lie_skew (D (D w)) (D w),
    ← lie_skew ⁅w, D (D w)⁆ (D w), neg_lie, lie_neg, neg_neg] at hJ
  simp only [map_add, map_sub, LieDerivation.apply_lie_eq_add, lie_add, lie_sub,
    lie_self, lie_zero, add_zero]
  rw [hJ]
  module

/-- The integral identity from the manuscript, in expanded operator form. -/
theorem derivation_identity (D : LieDerivation ℤ L L) (a : L) :
    let w := D a - (2 : ℤ) • a
    let f := D (D w) - w
    let g := ⁅a, D (D a)⁆ - ⁅w, ⁅w, D w⁆⁆
    let q := D ⁅a, f⁆ + ⁅w, f⁆
    let r := (3 : ℤ) • ⁅D w, ⁅w, f⁆⁆ + ⁅w, ⁅w, D f⁆⁆
    D (D (D g)) - (3 : ℤ) • D (D g) - D g + (3 : ℤ) • g =
      D q + q - D r + (3 : ℤ) • r := by
  dsimp only
  let w := D a - (2 : ℤ) • a
  let f := D (D w) - w
  let h := ⁅a, D (D a)⁆
  let c := ⁅w, ⁅w, D w⁆⁆
  let q := D ⁅a, f⁆ + ⁅w, f⁆
  let r := (3 : ℤ) • ⁅D w, ⁅w, f⁆⁆ + ⁅w, ⁅w, D f⁆⁆
  have hq : D (D h) = (4 : ℤ) • D h - (3 : ℤ) • h + q := by
    have he : D (D h) - (4 : ℤ) • D h + (3 : ℤ) • h = q :=
      derivation_quadratic_identity D a
    rw [← he]
    module
  have hc : D (D c) = c + r := by
    have he : D (D c) - c = r := derivation_cubic_identity D w
    rw [← he]
    module
  change D (D (D (h - c))) - (3 : ℤ) • D (D (h - c)) - D (h - c) +
    (3 : ℤ) • (h - c) = D q + q - D r + (3 : ℤ) • r
  simp only [map_sub, hq, hc, map_add, map_smul]
  module

def identityLeft (t z : L) : L :=
  ⁅t, ⁅t, ⁅t, z⁆⁆⁆ - (3 : ℤ) • ⁅t, ⁅t, z⁆⁆ - ⁅t, z⁆ + (3 : ℤ) • z

def identityRight (t a b : L) : L :=
  let q := ⁅t, ⁅a, b⁆⁆ + ⁅w t a, b⁆
  let r := (3 : ℤ) • ⁅⁅t, w t a⁆, ⁅w t a, b⁆⁆ + ⁅w t a, ⁅w t a, ⁅t, b⁆⁆⁆
  ⁅t, q⁆ + q - ⁅t, r⁆ + (3 : ℤ) • r

theorem integral_identity (t a : L) : identityLeft t (f₂ t a) = identityRight t a (f₁ t a) :=
  derivation_identity (ad t) a

theorem identityLeft_smul (t z : L) (n : ℤ) :
    identityLeft t (n • z) = n • identityLeft t z := by
  simp only [identityLeft, lie_smul, smul_sub, smul_add, smul_smul]
  module

theorem identityRight_smul (t a b : L) (n : ℤ) :
    identityRight t a (n • b) = n • identityRight t a b := by
  simp only [identityRight, lie_add, lie_smul, smul_sub, smul_add, smul_smul]
  module

/-- Dividing the identity requires only cancellation of multiplication by five. -/
theorem divided_identity (t a u v : L)
    (hinj : Function.Injective (fun z : L => (5 : ℤ) • z))
    (hu : (5 : ℤ) • u = f₁ t a) (hv : (5 : ℤ) • v = f₂ t a) :
    identityLeft t v = identityRight t a u := by
  apply hinj
  change (5 : ℤ) • identityLeft t v = (5 : ℤ) • identityRight t a u
  rw [← identityLeft_smul, ← identityRight_smul, hu, hv]
  exact integral_identity t a

variable {M : Type*} [LieRing M]

@[simp] theorem map_w (φ : L →ₗ⁅ℤ⁆ M) (t a : L) : φ (w t a) = w (φ t) (φ a) := by
  simp only [w, map_sub, map_smul, LieHom.map_lie]

@[simp] theorem map_f₁ (φ : L →ₗ⁅ℤ⁆ M) (t a : L) :
    φ (f₁ t a) = f₁ (φ t) (φ a) := by
  simp only [f₁, map_sub, LieHom.map_lie, map_w]

@[simp] theorem map_h (φ : L →ₗ⁅ℤ⁆ M) (t a : L) : φ (h t a) = h (φ t) (φ a) := by
  simp only [h, LieHom.map_lie]

@[simp] theorem map_c (φ : L →ₗ⁅ℤ⁆ M) (t a : L) : φ (c t a) = c (φ t) (φ a) := by
  simp only [c, LieHom.map_lie, map_w]

@[simp] theorem map_f₂ (φ : L →ₗ⁅ℤ⁆ M) (t a : L) :
    φ (f₂ t a) = f₂ (φ t) (φ a) := by
  simp only [f₂, map_sub, map_h, map_c]

section Scalar
variable {R : Type*} [CommRing R] [LieAlgebra R L]

@[simp] theorem w_smul (t a : L) (r : R) : w t (r • a) = r • w t a := by
  simp only [w, lie_smul, smul_sub, smul_comm r (2 : ℤ)]

@[simp] theorem f₁_smul (t a : L) (r : R) : f₁ t (r • a) = r • f₁ t a := by
  simp only [f₁, w_smul, lie_smul, smul_sub]

@[simp] theorem h_smul (t a : L) (r : R) : h t (r • a) = r ^ 2 • h t a := by
  simp only [h, lie_smul, smul_lie, smul_smul]
  congr 1
  ring

@[simp] theorem c_smul (t a : L) (r : R) : c t (r • a) = r ^ 3 • c t a := by
  simp only [c, w_smul, lie_smul, smul_lie, smul_smul]
  congr 1
  ring

end Scalar
end Parafree.TheoremB
