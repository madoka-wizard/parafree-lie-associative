import LieRings.UniversalEnveloping.Quotient

/-!
# The action span of a Lie ideal in its ambient enveloping algebra

The span of products with an ideal generator on the left is already a
 two-sided ideal. This identifies the coinvariants with the enveloping
algebra of the Lie quotient, without a basis or flatness hypothesis.
-/

noncomputable section

namespace Parafree.Associative.IdealCoinvariants

open LieRings

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (I : LieIdeal R L)

def span : Submodule R (UEA R L) :=
  Submodule.span R {a | ∃ x : I, ∃ b : UEA R L,
    UniversalEnvelopingAlgebra.ι R (x : L) * b = a}

theorem generator_mul_mem (x : I) (a : UEA R L) :
    UniversalEnvelopingAlgebra.ι R (x : L) * a ∈ span I :=
  Submodule.subset_span ⟨x, a, rfl⟩

theorem right_mul_mem {a : UEA R L} (ha : a ∈ span I) (b : UEA R L) :
    a * b ∈ span I := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨x, c, rfl⟩ := ha
    rw [mul_assoc]
    exact generator_mul_mem I x _
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (span I).add_mem ha hc
  | smul r a _ ha => simpa only [smul_mul_assoc] using (span I).smul_mem r ha

theorem iota_left_mul_mem (x : L) {a : UEA R L} (ha : a ∈ span I) :
    UniversalEnvelopingAlgebra.ι R x * a ∈ span I := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨j, b, rfl⟩ := ha
    have h : UniversalEnvelopingAlgebra.ι R x * (UniversalEnvelopingAlgebra.ι R (j : L) * b) =
        UniversalEnvelopingAlgebra.ι R ⁅x, (j : L)⁆ * b +
          UniversalEnvelopingAlgebra.ι R (j : L) * (UniversalEnvelopingAlgebra.ι R x * b) := by
      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      noncomm_ring
    rw [h]
    exact (span I).add_mem (generator_mul_mem I ⟨⁅x, (j : L)⁆, I.lie_mem j.property⟩ b)
      (generator_mul_mem I j _)
  | zero => simp
  | add a b _ _ ha hb => simpa only [mul_add] using (span I).add_mem ha hb
  | smul r a _ ha => simpa only [mul_smul_comm] using (span I).smul_mem r ha

theorem left_mul_mem (b : UEA R L) {a : UEA R L} (ha : a ∈ span I) :
    b * a ∈ span I := by
  induction b using UEA.induction generalizing a with
  | algebraMap r => simpa only [Algebra.smul_def] using (span I).smul_mem r ha
  | ι x => exact iota_left_mul_mem I x ha
  | add b c hb hc => simpa only [add_mul] using (span I).add_mem (hb ha) (hc ha)
  | mul b c hb hc => rw [mul_assoc]; exact hb (hc ha)

theorem span_eq_ideal : span I = (UEA.idealOfLieIdeal R L I).restrictScalars R := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨x, b, rfl⟩
    exact Ideal.mul_mem_right b _ (UEA.ι_mem_idealOfLieIdeal R L I x)
  · intro a ha
    change a ∈ TwoSidedIdeal.span (Set.range fun x : I =>
      UniversalEnvelopingAlgebra.ι R (x : L)) at ha
    induction ha using TwoSidedIdeal.span_induction with
    | mem a ha =>
      obtain ⟨x, rfl⟩ := ha
      simpa using generator_mul_mem I x 1
    | zero => exact (span I).zero_mem
    | add a b _ _ ha hb => exact (span I).add_mem ha hb
    | neg a _ ha => exact (span I).neg_mem ha
    | left_absorb b a _ ha => exact left_mul_mem I b ha
    | right_absorb b a _ ha => exact right_mul_mem I ha b

/-- The quotient by the ideal action is the enveloping algebra of the quotient. -/
def quotientEquiv : (UEA R L ⧸ span I) ≃ₗ[R] UEA R (L ⧸ I) :=
  (Submodule.quotEquivOfEq _ _ (span_eq_ideal I)).trans
    (UEA.quotientEquivLieIdeal R L I).symm.toLinearEquiv

end Parafree.Associative.IdealCoinvariants
