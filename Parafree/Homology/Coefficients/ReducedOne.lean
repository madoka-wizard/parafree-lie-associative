import Parafree.Homology.Coefficients.Coinvariants

/-! First coefficient homology as the kernel of the action on one-chains modulo
actual CE boundaries, together with its bilinear universal property. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Parafree.Homology.Coefficients

open CategoryTheory
open scoped TensorProduct
open Parafree.Linear.ExteriorTensor

variable (R G V : Type*) [CommRing R] [LieRing G] [LieAlgebra R G]
  [AddCommGroup V] [Module R V] [LieRingModule G V] [LieModule R G V]

omit [LieRingModule G V] [LieModule R G V] in
/-- Every coefficient chain is a linear combination of pure exterior tensors. -/
theorem pure_induction (n : ℕ) (P : Chain R G V n → Prop)
    (hzero : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (r : R) a, P a → P (r • a))
    (hpure : ∀ v m, P (pure R G V n v m)) (c : Chain R G V n) : P c := by
  induction c using TensorProduct.induction_on with
  | zero => exact hzero
  | add a b ha hb => exact hadd a b ha hb
  | tmul a m =>
    have ha : a ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
      rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
    refine Submodule.span_induction (p := fun a _ => P (a ⊗ₜ[R] m)) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨v, rfl⟩; exact hpure v m
    · simpa only [TensorProduct.zero_tmul] using hzero
    · intro a b _ _ ha hb
      simpa only [TensorProduct.add_tmul] using hadd _ _ ha hb
    · intro r a _ ha
      simpa only [TensorProduct.smul_tmul'] using hsmul r _ ha

omit [LieRingModule G V] [LieModule R G V] in
def oneChainEquiv : Chain R G V 1 ≃ₗ[R] G ⊗[R] V :=
  TensorProduct.congr (exteriorPower.oneEquiv R G) (LinearEquiv.refl R V)

omit [LieRingModule G V] [LieModule R G V] in
@[simp] theorem oneChainEquiv_pure (g : G) (v : V) :
    oneChainEquiv R G V (pure R G V 1 ![g] v) = g ⊗ₜ[R] v := by
  simp only [oneChainEquiv, pure, TensorProduct.congr_tmul, exteriorPower.oneEquiv_ιMulti,
    LinearEquiv.refl_apply, Matrix.cons_val_zero]

abbrev ReducedOne := Chain R G V 1 ⧸ (differential R G V 1).range

abbrev reducedOneClass : Chain R G V 1 →ₗ[R] ReducedOne R G V :=
  (differential R G V 1).range.mkQ

def reducedPair : G →ₗ[R] V →ₗ[R] ReducedOne R G V :=
  (TensorProduct.mk R G V).compr₂
    ((reducedOneClass R G V).comp (oneChainEquiv R G V).symm.toLinearMap)

@[simp] theorem reducedPair_apply (g : G) (v : V) :
    reducedPair R G V g v = reducedOneClass R G V (pure R G V 1 ![g] v) := by
  change reducedOneClass R G V ((oneChainEquiv R G V).symm (g ⊗ₜ[R] v)) = _
  rw [← oneChainEquiv_pure R G V g v, LinearEquiv.symm_apply_apply]
theorem reducedPair_relation (g h : G) (v : V) :
    reducedPair R G V ⁅g, h⁆ v + reducedPair R G V h ⁅g, v⁆ -
      reducedPair R G V g ⁅h, v⁆ = 0 := by
  have hz : reducedOneClass R G V (differential R G V 1 (pure R G V 2 ![g,h] v)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [differential_pure_two, map_add, map_sub, map_neg] at hz
  simp only [reducedPair_apply]
  apply neg_eq_zero.mp
  convert hz using 1; abel

variable {W : Type*} [AddCommGroup W] [Module R W]

def reducedOneLift (f : G →ₗ[R] V →ₗ[R] W)
    (hf : ∀ g h v, f ⁅g,h⁆ v + f h ⁅g,v⁆ - f g ⁅h,v⁆ = 0) :
    ReducedOne R G V →ₗ[R] W :=
  (differential R G V 1).range.liftQ
    ((TensorProduct.lift f).comp (oneChainEquiv R G V).toLinearMap) (by
      rintro _ ⟨c, rfl⟩
      change TensorProduct.lift f (oneChainEquiv R G V (differential R G V 1 c)) = 0
      refine pure_induction R G V 2
        (fun c => TensorProduct.lift f (oneChainEquiv R G V (differential R G V 1 c)) = 0)
        (by simp only [map_zero]) (by intros; simp_all only [map_add, add_zero])
        (by intros; simp_all only [map_smul, smul_zero]) ?_ c
      intro a v
      have ha : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
      rw [ha, differential_pure_two]
      simp only [map_add, map_sub, map_neg, oneChainEquiv_pure, TensorProduct.lift.tmul]
      calc
        -f ⁅a 0, a 1⁆ v - f (a 1) ⁅a 0, v⁆ + f (a 0) ⁅a 1, v⁆ =
          -(f ⁅a 0, a 1⁆ v + f (a 1) ⁅a 0, v⁆ - f (a 0) ⁅a 1, v⁆) := by abel
        _ = 0 := by rw [hf, neg_zero])

@[simp] theorem reducedOneLift_pair (f : G →ₗ[R] V →ₗ[R] W)
    (hf : ∀ g h v, f ⁅g,h⁆ v + f h ⁅g,v⁆ - f g ⁅h,v⁆ = 0) (g : G) (v : V) :
    reducedOneLift R G V f hf (reducedPair R G V g v) = f g v := by
  change TensorProduct.lift f (oneChainEquiv R G V (pure R G V 1 ![g] v)) = _
  rw [oneChainEquiv_pure, TensorProduct.lift.tmul]

/-- The induced action, with its sign adjusted from the CE differential. -/
def reducedAction : ReducedOne R G V →ₗ[R] V :=
  (differential R G V 1).range.liftQ
    (-((zeroChainEquiv R G V).toLinearMap.comp (differential R G V 0))) (by
      rintro _ ⟨c, rfl⟩
      change -(zeroChainEquiv R G V (differential R G V 0 (differential R G V 1 c))) = 0
      have hc : differential R G V 0 (differential R G V 1 c) = 0 :=
        LinearMap.congr_fun (differential_comp_differential R G V 0) c
      rw [hc, map_zero, neg_zero])

@[simp] theorem reducedAction_class (c : Chain R G V 1) :
    reducedAction R G V (reducedOneClass R G V c) =
      -zeroChainEquiv R G V (differential R G V 0 c) := rfl

@[simp] theorem reducedAction_pair (g : G) (v : V) :
    reducedAction R G V (reducedPair R G V g v) = ⁅g,v⁆ := by
  rw [reducedPair_apply, reducedAction_class, zeroChainEquiv_differential_pure, neg_neg]

abbrev firstCycles := LinearMap.ker (differential R G V 0)

def secondToFirstCycles : Chain R G V 2 →ₗ[R] firstCycles R G V :=
  (differential R G V 1).codRestrict _ (fun c =>
    LinearMap.congr_fun (differential_comp_differential R G V 0) c)

def firstCyclesToReducedKernel : firstCycles R G V →ₗ[R] LinearMap.ker (reducedAction R G V) :=
  ((reducedOneClass R G V).comp (firstCycles R G V).subtype).codRestrict _ (fun c => by
    change -zeroChainEquiv R G V (differential R G V 0 c) = 0
    rw [c.property, map_zero, neg_zero])

theorem firstCyclesToReducedKernel_surjective : Function.Surjective (firstCyclesToReducedKernel R G V) := by
  intro z
  obtain ⟨c, hc⟩ := (differential R G V 1).range.mkQ_surjective z.val
  have hz : differential R G V 0 c = 0 := by
    apply (zeroChainEquiv R G V).injective
    rw [map_zero]
    apply neg_eq_zero.mp
    exact (reducedAction_class R G V c).symm.trans ((congrArg (reducedAction R G V) hc).trans z.property)
  exact ⟨⟨c, hz⟩, Subtype.ext hc⟩

theorem firstCyclesToReducedKernel_ker :
    LinearMap.ker (firstCyclesToReducedKernel R G V) = (secondToFirstCycles R G V).range := by
  ext c
  constructor
  · intro hc
    have hz : reducedOneClass R G V c = 0 := congrArg Subtype.val hc
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    exact ⟨b, Subtype.ext hb⟩
  · rintro ⟨b, rfl⟩
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩

local instance : HasQuotient (firstCycles R G V) (Submodule R (firstCycles R G V)) :=
  Submodule.hasQuotient (R := R) (M := firstCycles R G V)

abbrev FirstHomology := firstCycles R G V ⧸ (secondToFirstCycles R G V).range

def firstHomologyEquivReducedKernel :
    FirstHomology R G V ≃ₗ[R] LinearMap.ker (reducedAction R G V) :=
  (Submodule.quotEquivOfEq _ _ (firstCyclesToReducedKernel_ker R G V).symm).trans
    ((firstCyclesToReducedKernel R G V).quotKerEquivOfSurjective
      (firstCyclesToReducedKernel_surjective R G V))
def homologyOneConcreteIso :
    homology R G V 1 ≅ ModuleCat.of R (FirstHomology R G V) :=
  (complex R G V).homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    ((complex R G V).sc' 2 1 0).moduleCatHomologyIso

/-- The left side is the homology of the all-degree coefficient CE complex. -/
def homologyOneEquivReducedKernel :
    Homology R G V 1 ≃ₗ[R] LinearMap.ker (reducedAction R G V) :=
  (homologyOneConcreteIso R G V).toLinearEquiv.trans (firstHomologyEquivReducedKernel R G V)

/-- Additive and scalar induction on the classes of pure one-chains. -/
theorem reducedOne_induction (P : ReducedOne R G V → Prop) (hzero : P 0)
    (hadd : ∀ a b, P a → P b → P (a+b)) (hsmul : ∀ (r : R) a, P a → P (r • a))
    (hpair : ∀ g v, P (reducedPair R G V g v)) (z : ReducedOne R G V) : P z := by
  obtain ⟨c,rfl⟩ := (differential R G V 1).range.mkQ_surjective z
  refine pure_induction R G V 1 (fun c => P (reducedOneClass R G V c))
    (by simpa only [map_zero] using hzero)
    (by intro a b ha hb; simpa only [map_add] using hadd _ _ ha hb)
    (by intro r a ha; simpa only [map_smul] using hsmul r _ ha) ?_ c
  intro a v
  have ha : a = ![a 0] := by ext i; fin_cases i; rfl
  rw [ha]
  exact hpair (a 0) v

theorem reducedOne_ext {f h : ReducedOne R G V →ₗ[R] W}
    (he : ∀ g v, f (reducedPair R G V g v) = h (reducedPair R G V g v)) : f = h := by
  apply LinearMap.ext
  intro z
  exact reducedOne_induction R G V (fun z => f z = h z)
    (by simp only [map_zero]) (by intros; simp_all only [map_add])
    (by intros; simp_all only [map_smul]) he z
end Parafree.Homology.Coefficients
