import Parafree.Homology.ReducedExteriorExactness
import Parafree.Homology.Coefficients.ReducedOne
import Parafree.Lie.DerivedStable

/-! Explicit data for a split Lie extension whose kernel abelianization has an
equivariant linear section.  No homology comparison is included as a field. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Parafree.Homology.SplitExtension

open LieRings.Homological.LieHomology
open Parafree.Lie

variable (R G E V : Type*) [CommRing R] [LieRing G] [LieAlgebra R G]
  [LieRing E] [LieAlgebra R E] [AddCommGroup V] [Module R V]
  [LieRingModule G V]

structure Data where
  ideal : LieIdeal R E
  base : G →ₗ⁅R⁆ E
  quotient : E →ₗ⁅R⁆ G
  part : E →ₗ[R] ideal
  quotient_base : ∀ g, quotient (base g) = g
  quotient_ideal : ∀ f : ideal, quotient f = 0
  part_base : ∀ g, part (base g) = 0
  part_ideal : ∀ f : ideal, part f = f
  decomposition : ∀ x, x = base (quotient x) + (part x : E)
  projection : ideal →ₗ[R] V
  coefficientSection : V →ₗ[R] ideal
  projection_section : ∀ v, projection (coefficientSection v) = v
  projection_ker : ∀ f, projection f = 0 ↔ f ∈ derivedSubmodule R ideal
  section_equivariant : ∀ g v, ⁅base g,coefficientSection v⁆ = coefficientSection ⁅g,v⁆

namespace Data

variable {R G E V}
variable (S : Data R G E V)

@[simp] theorem projection_lie (g : G) (f : S.ideal) :
    S.projection ⁅S.base g,f⁆ = ⁅g,S.projection f⁆ :=
  projection_equivariant_of_section S.ideal S.base S.projection S.coefficientSection
    S.projection_section S.projection_ker S.section_equivariant g f

@[simp] theorem projection_bracket (f t : S.ideal) : S.projection ⁅f,t⁆ = 0 :=
  (S.projection_ker _).mpr
    (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _))

@[simp] theorem part_mixed (g : G) (f : S.ideal) : S.part ⁅S.base g,(f : E)⁆ = ⁅S.base g,f⁆ :=
  S.part_ideal ⁅S.base g,f⁆

@[simp] theorem part_bracket (f t : S.ideal) : S.part ⁅(f : E),(t : E)⁆ = ⁅f,t⁆ :=
  S.part_ideal ⁅f,t⁆

theorem part_lie (x y : E) : S.part ⁅x,y⁆ =
    ⁅S.base (S.quotient x),S.part y⁆ - ⁅S.base (S.quotient y),S.part x⁆ + ⁅S.part x,S.part y⁆ := by
  calc
    S.part ⁅x,y⁆ = S.part ⁅S.base (S.quotient x) + (S.part x : E),
      S.base (S.quotient y) + (S.part y : E)⁆ :=
        congrArg S.part (congrArg₂ (fun a b : E => ⁅a,b⁆) (S.decomposition x) (S.decomposition y))
    _ = _ := by
      rw [add_lie, lie_add, lie_add, map_add, map_add, map_add,
        ← S.base.map_lie, S.part_base, zero_add, part_mixed, part_bracket,
        ← lie_skew (S.part x : E) (S.base (S.quotient y)), map_neg, part_mixed]
      abel

def abelianPart : E →ₗ[R] V := S.projection.comp S.part

@[simp] theorem abelianPart_base (g : G) : S.abelianPart (S.base g) = 0 := by
  change S.projection (S.part (S.base g)) = 0
  rw [S.part_base, map_zero]

@[simp] theorem abelianPart_ideal (f : S.ideal) : S.abelianPart (f : E) = S.projection f := by
  change S.projection (S.part f) = S.projection f
  rw [S.part_ideal]

theorem abelianPart_lie (x y : E) :
    S.abelianPart ⁅x,y⁆ = ⁅S.quotient x,S.abelianPart y⁆ - ⁅S.quotient y,S.abelianPart x⁆ := by
  change S.projection (S.part ⁅x,y⁆) = _
  rw [part_lie, map_add, map_sub, projection_lie, projection_lie, projection_bracket, add_zero]
  rfl

end Data
end Parafree.Homology.SplitExtension
