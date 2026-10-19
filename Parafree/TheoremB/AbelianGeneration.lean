import Parafree.TheoremB.Model

/-! Abelian generation by the two elements in the stated para-equivalence.
The divided integral identity proves that the fourth generator is a commutator. -/

noncomputable section
namespace Parafree.TheoremB

open Parafree.Lie

theorem five_u : (5 : ℤ) • u = f₁ t a := by
  apply Subtype.ext
  change (5 : ℤ) • ((1 / 5 : ℚ) • f₁ ambientT ambientA) = f₁ ambientT ambientA
  norm_num [← Int.cast_smul_eq_zsmul ℚ, smul_smul]

theorem five_v : (5 : ℤ) • v = f₂ t a := by
  apply Subtype.ext
  change (5 : ℤ) • ((1 / 5 : ℚ) • f₂ ambientT ambientA) = f₂ ambientT ambientA
  norm_num [← Int.cast_smul_eq_zsmul ℚ, smul_smul]

theorem five_smul_injective : Function.Injective (fun z : P => (5 : ℤ) • z) := by
  intro b d he
  apply Subtype.ext
  have hh := congrArg (fun z : P => (1 / 5 : ℚ) • (z : Ambient)) he
  change (1 / 5 : ℚ) • ((5 : ℤ) • (b : Ambient)) =
    (1 / 5 : ℚ) • ((5 : ℤ) • (d : Ambient)) at hh
  simpa only [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_ofNat,
    div_mul_cancel₀ _ (by norm_num : (5 : ℚ) ≠ 0), one_smul] using hh

abbrev Abelianization := P ⧸ lowerCentral ℤ P 1

def abelianProjection : P →ₗ⁅ℤ⁆ Abelianization := quotientMk _

@[simp] theorem abelian_lie (b d : Abelianization) : ⁅b, d⁆ = 0 :=
  lie_eq_zero_of_lowerCentral_one (lowerCentral_quotient_eq_bot 1) b d

theorem abelian_v : abelianProjection v = 0 := by
  have hi := congrArg abelianProjection
    (divided_identity t a u v five_smul_injective five_u five_v)
  have h3 : (3 : ℤ) • abelianProjection v = 0 := by
    simpa only [identityLeft, identityRight, map_sub, map_add, map_smul,
      LieHom.map_lie, abelian_lie, sub_zero, zero_sub, zero_add, add_zero,
      smul_zero, neg_zero] using hi
  have h5 : (5 : ℤ) • abelianProjection v = 0 := by
    simpa only [map_smul, map_sub, LieHom.map_lie, f₂, h, c, abelian_lie, sub_self] using
      congrArg abelianProjection five_v
  calc
    abelianProjection v = (2 : ℤ) • ((3 : ℤ) • abelianProjection v) -
        (5 : ℤ) • abelianProjection v := by module
    _ = 0 := by rw [h3, h5, smul_zero, sub_self]

theorem abelian_five_u : (5 : ℤ) • abelianProjection u = (2 : ℤ) • abelianProjection a := by
  simpa only [map_smul, map_sub, LieHom.map_lie, f₁, w, abelian_lie, zero_sub, neg_neg] using
    congrArg abelianProjection five_u

theorem abelian_a : abelianProjection a = (5 : ℤ) • abelianProjection x := by
  change _ = (5 : ℤ) • abelianProjection (a - (2 : ℤ) • u)
  rw [map_sub, map_smul]
  calc
    abelianProjection a = (5 : ℤ) • abelianProjection a -
        (2 : ℤ) • ((2 : ℤ) • abelianProjection a) := by module
    _ = _ := by rw [← abelian_five_u]; module

theorem abelian_u : abelianProjection u = (2 : ℤ) • abelianProjection x := by
  change _ = (2 : ℤ) • abelianProjection (a - (2 : ℤ) • u)
  rw [map_sub, map_smul]
  calc
    abelianProjection u = (5 : ℤ) • abelianProjection u -
        (4 : ℤ) • abelianProjection u := by module
    _ = _ := by rw [abelian_five_u]; module

/-- A map out of the Lie subring is determined by the four specified generators. -/
theorem hom_ext {M : Type*} [LieRing M] (φ ψ : P →ₗ⁅ℤ⁆ M)
    (he : ∀ i, φ (generator i) = ψ (generator i)) : φ = ψ := by
  ext z
  obtain ⟨z, hz⟩ := z
  induction hz using LieSubalgebra.lieSpan_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact he i
  | zero => exact (map_zero φ).trans (map_zero ψ).symm
  | add b d hb hd ihb ihd =>
    change φ (⟨b, hb⟩ + ⟨d, hd⟩) = ψ (⟨b, hb⟩ + ⟨d, hd⟩)
    rw [map_add, map_add, ihb, ihd]
  | smul r b hb ih =>
    change φ (r • ⟨b, hb⟩) = ψ (r • ⟨b, hb⟩)
    rw [map_smul, map_smul, ih]
  | lie b d hb hd ihb ihd =>
    change φ ⁅(⟨b, hb⟩ : P), (⟨d, hd⟩ : P)⁆ = ψ ⁅(⟨b, hb⟩ : P), (⟨d, hd⟩ : P)⁆
    rw [LieHom.map_lie, LieHom.map_lie, ihb, ihd]

/-- Once five is cancellable in the target, the images of `t` and `a`
determine a homomorphism, including the two divided relators. -/
theorem hom_ext_of_five_smul_injective {M : Type*} [LieRing M]
    (hinj : Function.Injective (fun z : M => (5 : ℤ) • z))
    (φ ψ : P →ₗ⁅ℤ⁆ M) (ht : φ t = ψ t) (ha : φ a = ψ a) : φ = ψ := by
  apply hom_ext
  intro i
  fin_cases i
  · exact ht
  · exact ha
  · apply hinj
    change (5 : ℤ) • φ u = (5 : ℤ) • ψ u
    rw [← map_smul, ← map_smul, five_u, map_f₁, map_f₁, ht, ha]
  · apply hinj
    change (5 : ℤ) • φ v = (5 : ℤ) • ψ v
    rw [← map_smul, ← map_smul, five_v, map_f₂, map_f₂, ht, ha]

theorem abelian_freeToP_surjective : Function.Surjective (nilpotentMap freeToP 1) := by
  let φ := abelianProjection.comp freeToP
  have hg (i : Fin 4) : abelianProjection (generator i) ∈ φ.range := by
    fin_cases i
    · exact ⟨integralT, congrArg abelianProjection (FreeLieAlgebra.lift_of_apply _ _)⟩
    · refine ⟨(5 : ℤ) • integralA, ?_⟩
      change abelianProjection (freeToP ((5 : ℤ) • integralA)) = abelianProjection a
      rw [map_smul, show freeToP integralA = x from FreeLieAlgebra.lift_of_apply _ _, map_smul]
      exact abelian_a.symm
    · refine ⟨(2 : ℤ) • integralA, ?_⟩
      change abelianProjection (freeToP ((2 : ℤ) • integralA)) = abelianProjection u
      rw [map_smul, show freeToP integralA = x from FreeLieAlgebra.lift_of_apply _ _, map_smul]
      exact abelian_u.symm
    · exact ⟨0, by simpa using abelian_v.symm⟩
  have hr (z : P) : abelianProjection z ∈ φ.range := by
    obtain ⟨z, hz⟩ := z
    induction hz using LieSubalgebra.lieSpan_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hg i
    | zero => simpa only [map_zero] using φ.range.zero_mem
    | add b d hb hd ihb ihd =>
      change abelianProjection (⟨b, hb⟩ + ⟨d, hd⟩) ∈ φ.range
      simpa only [map_add] using φ.range.add_mem ihb ihd
    | smul r b hb ih =>
      change abelianProjection (r • ⟨b, hb⟩) ∈ φ.range
      simpa only [map_smul] using φ.range.smul_mem r ih
    | lie b d hb hd ihb ihd =>
      change abelianProjection ⁅(⟨b, hb⟩ : P), (⟨d, hd⟩ : P)⁆ ∈ φ.range
      simpa only [LieHom.map_lie] using φ.range.lie_mem ihb ihd
  intro z
  obtain ⟨b, rfl⟩ := quotientMk_surjective (lowerCentral ℤ P 1) z
  obtain ⟨d, hd⟩ := hr b
  exact ⟨quotientMk _ d, hd⟩

end Parafree.TheoremB
