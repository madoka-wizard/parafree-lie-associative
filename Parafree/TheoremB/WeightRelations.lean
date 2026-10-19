import Parafree.TheoremB.SolvableRelations

/-! Integral changes of generators and weight separation for the auxiliary
presentation. Denominators are avoided until the coefficient ring is chosen. -/

namespace Parafree.TheoremB.WeightRelations

variable {L : Type*} [LieRing L]

def s (t a : L) : L := -⁅t, w t a⁆ - w t a
def e (t a : L) : L := ⁅t, ⁅t, a⁆⁆ - a
def m (t a : L) : L := ⁅t, w t a⁆ - w t a

theorem generators_identity (t a : L) :
    (3 : ℤ) • s t a + (2 : ℤ) • e t a + m t a = (6 : ℤ) • a := by
  simp only [s, e, m, w, lie_sub, lie_smul]
  module

theorem s_weight_error (t a : L) : ⁅t, s t a⁆ - s t a = -f₁ t a := by
  simp only [s, f₁, lie_sub, lie_neg]
  module

theorem e_weight_error (t a : L) : ⁅t, e t a⁆ - (2 : ℤ) • e t a = f₁ t a := by
  simp only [e, f₁, w, lie_sub, lie_smul]
  module

theorem m_weight_error (t a : L) : ⁅t, m t a⁆ + m t a = f₁ t a := by
  simp only [m, f₁, lie_sub]
  module

private theorem quadratic (t a : L) :
    (6 : ℤ) • h t a = (3 : ℤ) • ⁅s t a, e t a⁆ - ⁅e t a, m t a⁆ := by
  simp only [h, s, e, m, w, lie_sub, sub_lie, lie_smul, smul_lie,
    neg_lie, lie_self, zero_sub, sub_zero,
    ← lie_skew ⁅t, ⁅t, a⁆⁆ a, ← lie_skew ⁅t, a⁆ a,
    ← lie_skew ⁅t, ⁅t, a⁆⁆ ⁅t, a⁆]
  module

private theorem cubic (t a : L) :
    (4 : ℤ) • c t a = ⁅s t a, ⁅s t a, m t a⁆⁆ + ⁅m t a, ⁅s t a, m t a⁆⁆ := by
  have hs : s t a + m t a = (-2 : ℤ) • w t a := by simp only [s, m]; module
  have hb : ⁅s t a, m t a⁆ = (-2 : ℤ) • ⁅w t a, ⁅t, w t a⁆⁆ := by
    simp only [s, m, sub_lie, neg_lie, lie_sub, lie_self,
      ← lie_skew ⁅t, w t a⁆ (w t a), neg_neg]
    module
  rw [← add_lie, hs, hb, smul_lie, lie_smul, smul_smul]
  rfl

/-- Exact relation expansion; this identity holds even before imposing `f₁ = 0`. -/
theorem relator_expansion (t a : L) :
    (12 : ℤ) • f₂ t a = (6 : ℤ) • ⁅s t a, e t a⁆ -
      ((2 : ℤ) • ⁅e t a, m t a⁆ + (3 : ℤ) • ⁅s t a, ⁅s t a, m t a⁆⁆) -
      (3 : ℤ) • ⁅m t a, ⁅s t a, m t a⁆⁆ := by
  calc
    (12 : ℤ) • f₂ t a = (2 : ℤ) • ((6 : ℤ) • h t a) -
        (3 : ℤ) • ((4 : ℤ) • c t a) := by simp only [f₂]; module
    _ = _ := by rw [quadratic, cubic]; module

/-- Separation of three weights using only cancellation of multiplication by two. -/
private theorem separate (D : LieDerivation ℤ L L) (A B C : L)
    (h2 : Function.Injective (fun z : L => (2 : ℤ) • z))
    (hA : D A = (3 : ℤ) • A) (hB : D B = B) (hC : D C = -C)
    (he : A - B - C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have he1 : (3 : ℤ) • A - B + C = 0 := by
    simpa only [map_sub, hA, hB, hC, sub_neg_eq_add, map_zero] using congrArg D he
  have he2 : (9 : ℤ) • A - B - C = 0 := by
    have hd := congrArg D he1
    simpa only [map_add, map_sub, map_smul, hA, hB, hC, map_zero, smul_smul,
      show (3 : ℤ) * 3 = 9 from rfl, ← sub_eq_add_neg] using hd
  have h8 : (8 : ℤ) • A = 0 := by
    calc
      (8 : ℤ) • A = ((9 : ℤ) • A - B - C) - (A - B - C) := by module
      _ = 0 := by rw [he2, he, sub_self]
  have ha : A = 0 := by
    apply h2
    apply h2
    apply h2
    change (2 : ℤ) • ((2 : ℤ) • ((2 : ℤ) • A)) = (2 : ℤ) • ((2 : ℤ) • ((2 : ℤ) • (0 : L)))
    simpa only [smul_smul, smul_zero] using h8
  have hB2 : (2 : ℤ) • B = 0 := by
    calc
      (2 : ℤ) • B = (4 : ℤ) • A - ((3 : ℤ) • A - B + C) - (A - B - C) := by module
      _ = 0 := by rw [he1, he, ha]; simp only [smul_zero, sub_zero]
  have hb : B = 0 := h2 (by simpa only [smul_zero] using hB2)
  refine ⟨ha, hb, ?_⟩
  simpa only [ha, hb, sub_zero, zero_sub, neg_eq_zero] using he

/-- The two original relators imply the three finite solvable relations whenever
two and three are cancellable. This applies over the integers localized at five
and over the field with five elements. -/
theorem solvable_relations (t a : L)
    (h2 : Function.Injective (fun z : L => (2 : ℤ) • z))
    (h3 : Function.Injective (fun z : L => (3 : ℤ) • z))
    (hf₁ : f₁ t a = 0) (hf₂ : f₂ t a = 0) :
    ⁅s t a, e t a⁆ = 0 ∧
      (2 : ℤ) • ⁅e t a, m t a⁆ + (3 : ℤ) • ⁅s t a, ⁅s t a, m t a⁆⁆ = 0 ∧
      ⁅m t a, ⁅s t a, m t a⁆⁆ = 0 := by
  have hs : ⁅t, s t a⁆ = s t a := by
    have hh := s_weight_error t a
    rw [hf₁, neg_zero, sub_eq_zero] at hh
    exact hh
  have he : ⁅t, e t a⁆ = (2 : ℤ) • e t a := by
    have hh := e_weight_error t a
    rw [hf₁, sub_eq_zero] at hh
    exact hh
  have hm : ⁅t, m t a⁆ = -m t a := by
    have hh := m_weight_error t a
    rw [hf₁] at hh
    exact eq_neg_of_add_eq_zero_left hh
  obtain ⟨ha, hb, hc⟩ := separate (ad t)
    ((6 : ℤ) • ⁅s t a, e t a⁆)
    ((2 : ℤ) • ⁅e t a, m t a⁆ + (3 : ℤ) • ⁅s t a, ⁅s t a, m t a⁆⁆)
    ((3 : ℤ) • ⁅m t a, ⁅s t a, m t a⁆⁆) h2
    (by simp only [ad_apply, lie_smul, leibniz_lie t, hs, he]; module)
    (by simp only [ad_apply, lie_add, lie_smul, leibniz_lie t, hs, he, hm,
          smul_lie, lie_neg]; module)
    (by simp only [ad_apply, lie_smul, leibniz_lie t, hs, hm, lie_neg, neg_lie,
          lie_add]; module)
    (by rw [← relator_expansion, hf₂, smul_zero])
  refine ⟨?_, hb, ?_⟩
  · apply h3
    apply h2
    change (2 : ℤ) • ((3 : ℤ) • ⁅s t a, e t a⁆) = (2 : ℤ) • ((3 : ℤ) • (0 : L))
    simpa only [smul_smul, smul_zero] using ha
  · apply h3
    change (3 : ℤ) • ⁅m t a, ⁅s t a, m t a⁆⁆ = (3 : ℤ) • (0 : L)
    simpa only [smul_zero] using hc

end Parafree.TheoremB.WeightRelations
