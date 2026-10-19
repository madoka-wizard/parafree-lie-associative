import Parafree.Lie.DerivedReduction

/-! Stability of an ideal's intrinsic derived submodule under ambient adjoints.
An equivariant section of its abelianization makes the quotient projection
equivariant as well. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Parafree.Lie

variable {R E : Type*} [CommRing R] [LieRing E] [LieAlgebra R E]

/-- Ambient adjoints preserve the intrinsic derived submodule of an ideal. -/
theorem ideal_adjoint_mem_derived (I : LieIdeal R E) (x : E) {y : I}
    (hy : y ∈ derivedSubmodule R I) : ⁅x,y⁆ ∈ derivedSubmodule R I := by
  rw [derivedSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hy
  refine Submodule.span_induction
    (p := fun y _ => ⁅x,y⁆ ∈ derivedSubmodule R I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, _, b, _, rfl⟩
    have he : ⁅x, ⁅a,b⁆⁆ = ⁅⁅x,a⁆,b⁆ + ⁅a,⁅x,b⁆⁆ := by
      apply Subtype.ext
      exact leibniz_lie x (a : E) (b : E)
    rw [he]
    exact (derivedSubmodule R I).add_mem
      (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _))
      (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _))
  · change ⁅x,(0 : I)⁆ ∈ derivedSubmodule R I
    rw [show ⁅x,(0 : I)⁆ = 0 from lie_zero x]; exact (derivedSubmodule R I).zero_mem
  · intro a b _ _ ha hb
    rw [show ⁅x,a+b⁆ = ⁅x,a⁆ + ⁅x,b⁆ from lie_add x a b]; exact (derivedSubmodule R I).add_mem ha hb
  · intro r a _ ha
    rw [show ⁅x,r • a⁆ = r • ⁅x,a⁆ from lie_smul r x a]; exact (derivedSubmodule R I).smul_mem r ha

variable {G V : Type*} [LieRing G] [LieAlgebra R G]
  [AddCommGroup V] [Module R V] [LieRingModule G V] [LieModule R G V]

omit [LieModule R G V] in
theorem projection_equivariant_of_section (I : LieIdeal R E) (base : G →ₗ⁅R⁆ E)
    (p : I →ₗ[R] V) (s : V →ₗ[R] I) (hs : ∀ v, p (s v) = v)
    (hker : ∀ f, p f = 0 ↔ f ∈ derivedSubmodule R I)
    (heq : ∀ g v, ⁅base g, s v⁆ = s ⁅g,v⁆) (g : G) (f : I) :
    p ⁅base g,f⁆ = ⁅g,p f⁆ := by
  have hd : f - s (p f) ∈ derivedSubmodule R I :=
    (hker _).mp (by
      calc
        p (f - s (p f)) = p f - p (s (p f)) := map_sub p f (s (p f))
        _ = 0 := by rw [hs, sub_self])
  have hz := (hker _).mpr (ideal_adjoint_mem_derived I (base g) hd)
  apply sub_eq_zero.mp
  calc
    p ⁅base g,f⁆ - ⁅g,p f⁆ = p ⁅base g,f⁆ - p ⁅base g,s (p f)⁆ := by rw [heq, hs]
    _ = p (⁅base g,f⁆ - ⁅base g,s (p f)⁆) := (map_sub p _ _).symm
    _ = p ⁅base g,f-s (p f)⁆ := congrArg p (lie_sub (base g) f (s (p f))).symm
    _ = 0 := hz

end Parafree.Lie
