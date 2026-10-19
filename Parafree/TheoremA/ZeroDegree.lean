import Parafree.TheoremA.GradedSplit
import Parafree.TheoremA.AuxiliaryQuotient

/-! The degree-zero quotient of the actual reduced grading is the signed
rank-three auxiliary Lie algebra, with an explicit splitting. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie Parafree.Linear
open Auxiliary

/-- The ambient integral free Lie algebra maps into degree zero. -/
def zeroClassHom : Auxiliary.Free ℤ →ₗ⁅ℤ⁆ ReducedGraded where
  __ := (DFinsupp.lsingle 0).comp ((reducedLayerRelations 0).mkQ.comp
    ((LinearMap.id : Auxiliary.Free ℤ →ₗ[ℤ] _).codRestrict (dividedFiltration 0)
      (fun _ => Submodule.mem_top)))
  map_lie' {x y} := by
    change gradedClass 0 ⟨⁅x, y⁆, Submodule.mem_top⟩ =
      ⁅gradedClass 0 ⟨x, Submodule.mem_top⟩, gradedClass 0 ⟨y, Submodule.mem_top⟩⁆
    exact (gradedClass_lie 0 0 ⟨x, Submodule.mem_top⟩ ⟨y, Submodule.mem_top⟩).symm

theorem zeroClassHom_of_mem {x : Auxiliary.Free ℤ} (hx : x ∈ Auxiliary.relationIdeal ℤ) :
    zeroClassHom x = 0 := by
  have he : x ∈ dividedFiltration 1 :=
    (mem_dividedFiltration_succ 0 x).mpr ⟨hx, LieSubmodule.mem_top _⟩
  have hq : (reducedLayerRelations 0).mkQ (⟨x, Submodule.mem_top⟩ : dividedFiltration 0) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (show _ ∈ reducedLayerRelations 0 from (le_sup_left : integralLayerRelations 0 ≤ reducedLayerRelations 0) he)
  change (DFinsupp.single 0 ((reducedLayerRelations 0).mkQ ⟨x, Submodule.mem_top⟩) : ReducedGraded) = 0
  rw [hq, DFinsupp.single_zero]

def zeroIntegralHom : Presented ℤ →ₗ⁅ℤ⁆ ReducedGraded :=
  quotientLift (Auxiliary.relationIdeal ℤ) zeroClassHom (fun _ hx => zeroClassHom_of_mem hx)

def zeroDegreeSection : CrossProduct (ZMod 2) →ₗ⁅ZMod 2⁆ ReducedGraded :=
  CrossProduct.lift (ZMod 2) (zeroIntegralHom (gen ℤ 0))
    (zeroIntegralHom (gen ℤ 1)) (zeroIntegralHom (gen ℤ 2))
    (by rw [← LieHom.map_lie, lie_gen_one_two])
    (by rw [← LieHom.map_lie, lie_gen_two_zero])
    (by rw [← LieHom.map_lie, lie_gen_zero_one, map_neg])

@[simp] theorem zeroDegreeSection_z :
    zeroDegreeSection (CrossProduct.z (ZMod 2)) = zeroClassHom (generator ℤ 0) :=
  CrossProduct.lift_z _ _ _ _ _ _ _
@[simp] theorem zeroDegreeSection_u :
    zeroDegreeSection (CrossProduct.u (ZMod 2)) = zeroClassHom (generator ℤ 1) :=
  CrossProduct.lift_u _ _ _ _ _ _ _
@[simp] theorem zeroDegreeSection_v :
    zeroDegreeSection (CrossProduct.v (ZMod 2)) = zeroClassHom (generator ℤ 2) :=
  CrossProduct.lift_v _ _ _ _ _ _ _

def freeFieldEvaluation : Auxiliary.Free ℤ →ₗ⁅ℤ⁆ CrossProduct (ZMod 2) :=
  AuxiliaryQuotient.coefficientMap.comp (freeEvaluation ℤ)

@[simp] theorem freeFieldEvaluation_generator (i : Fin 3) :
    freeFieldEvaluation (generator ℤ i) =
      ![CrossProduct.z (ZMod 2), CrossProduct.u (ZMod 2), CrossProduct.v (ZMod 2)] i := by
  change AuxiliaryQuotient.coefficientMap (freeEvaluation ℤ (generator ℤ i)) = _
  rw [freeEvaluation_generator]
  fin_cases i
  · exact CrossProduct.lift_z _ _ _ _ _ _ _
  · exact CrossProduct.lift_u _ _ _ _ _ _ _
  · exact CrossProduct.lift_v _ _ _ _ _ _ _

theorem freeFieldEvaluation_of_mem {x : Auxiliary.Free ℤ}
    (hx : x ∈ Auxiliary.relationIdeal ℤ) : freeFieldEvaluation x = 0 := by
  have h : freeEvaluation ℤ x = 0 := by
    change toCrossProduct ℤ (quotientMk (Auxiliary.relationIdeal ℤ) x) = 0
    rw [(quotientMk_eq_zero _ _).mpr hx, map_zero]
  change AuxiliaryQuotient.coefficientMap (freeEvaluation ℤ x) = 0
  rw [h, map_zero]

theorem crossProduct_two_smul (x : CrossProduct (ZMod 2)) : (2 : ℤ) • x = 0 := by
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_smul]

def zeroLayerEvaluation : ReducedLayer 0 →ₗ[ℤ] CrossProduct (ZMod 2) :=
  (reducedLayerRelations 0).liftQ
    (freeFieldEvaluation.toLinearMap.comp (dividedFiltration 0).subtype) (by
      intro x hx
      obtain ⟨a, ha, b, _, he⟩ := (mem_reducedLayerRelations 0 x).mp hx
      obtain ⟨haJ, _⟩ := (mem_dividedFiltration_succ 0 a).mp ha
      change freeFieldEvaluation (x : Auxiliary.Free ℤ) = 0
      rw [he, map_add, freeFieldEvaluation_of_mem haJ, zero_add, map_smul,
        crossProduct_two_smul])

def zeroDegreeLinear : ReducedGraded →ₗ[ℤ] CrossProduct (ZMod 2) :=
  zeroLayerEvaluation.comp (DFinsupp.lapply 0)

@[simp] theorem zeroDegreeLinear_class_zero (a : dividedFiltration 0) :
    zeroDegreeLinear (gradedClass 0 a) = freeFieldEvaluation a := by
  change zeroLayerEvaluation ((DFinsupp.single 0 ((reducedLayerRelations 0).mkQ a) : ReducedGraded) 0) = _
  rw [DFinsupp.single_eq_same]
  rfl

theorem zeroDegreeLinear_class_of_ne (n : ℕ) (hn : n ≠ 0) (a : dividedFiltration n) :
    zeroDegreeLinear (gradedClass n a) = 0 := by
  change zeroLayerEvaluation ((DFinsupp.single n ((reducedLayerRelations n).mkQ a) : ReducedGraded) 0) = _
  rw [DFinsupp.single_eq_of_ne hn.symm, map_zero]

theorem zeroDegreeLinear_lie_class (i j : ℕ) (a : dividedFiltration i) (b : dividedFiltration j) :
    zeroDegreeLinear ⁅gradedClass i a, gradedClass j b⁆ =
      ⁅zeroDegreeLinear (gradedClass i a), zeroDegreeLinear (gradedClass j b)⁆ := by
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      rw [gradedClass_lie, zeroDegreeLinear_class_zero,
        zeroDegreeLinear_class_zero, zeroDegreeLinear_class_zero]
      exact freeFieldEvaluation.map_lie _ _
    · rw [gradedClass_lie, zeroDegreeLinear_class_of_ne _ (by omega),
        zeroDegreeLinear_class_of_ne j hj, lie_zero]
  · rw [gradedClass_lie, zeroDegreeLinear_class_of_ne _ (by omega),
      zeroDegreeLinear_class_of_ne i hi, zero_lie]

theorem zeroDegreeLinear_lie (x y : ReducedGraded) :
    zeroDegreeLinear ⁅x, y⁆ = ⁅zeroDegreeLinear x, zeroDegreeLinear y⁆ := by
  refine graded_induction
    (fun x => zeroDegreeLinear ⁅x, y⁆ = ⁅zeroDegreeLinear x, zeroDegreeLinear y⁆) ?_ ?_ ?_ x
  · simp only [zero_lie, map_zero]
  · intro a b ha hb
    simp only [add_lie, map_add, ha, hb]
  · intro i a
    refine graded_induction
      (fun y => zeroDegreeLinear ⁅gradedClass i a, y⁆ =
        ⁅zeroDegreeLinear (gradedClass i a), zeroDegreeLinear y⁆) ?_ ?_ ?_ y
    · simp only [lie_zero, map_zero]
    · intro b c hb hc
      simp only [lie_add, map_add, hb, hc]
    · intro j b
      exact zeroDegreeLinear_lie_class i j a b

def zeroDegreeMap : ReducedGraded →ₗ⁅ZMod 2⁆ CrossProduct (ZMod 2) :=
  { zeroDegreeLinear.toAddMonoidHom.toZModLinearMap 2 with map_lie' := zeroDegreeLinear_lie _ _ }

@[simp] theorem zeroDegreeMap_zeroClass (x : Auxiliary.Free ℤ) :
    zeroDegreeMap (zeroClassHom x) = freeFieldEvaluation x :=
  zeroDegreeLinear_class_zero ⟨x, Submodule.mem_top⟩

theorem zeroDegreeMap_section : zeroDegreeMap.comp zeroDegreeSection = LieHom.id := by
  apply CrossProduct.hom_ext
  all_goals simp only [LieHom.comp_apply, zeroDegreeSection_z, zeroDegreeSection_u,
    zeroDegreeSection_v, zeroDegreeMap_zeroClass, freeFieldEvaluation_generator,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, LieHom.id_apply]
  rfl

theorem zeroDegreeSection_evaluation (x : Auxiliary.Free ℤ) :
    zeroDegreeSection (freeFieldEvaluation x) = zeroClassHom x := by
  let s : CrossProduct (ZMod 2) →ₗ⁅ℤ⁆ ReducedGraded :=
    { zeroDegreeSection.toLinearMap.restrictScalars ℤ with map_lie' := zeroDegreeSection.map_lie _ _ }
  have h : s.comp freeFieldEvaluation = zeroClassHom := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change zeroDegreeSection (freeFieldEvaluation (generator ℤ i)) = zeroClassHom (generator ℤ i)
    rw [freeFieldEvaluation_generator]
    fin_cases i
    · exact zeroDegreeSection_z
    · exact zeroDegreeSection_u
    · exact zeroDegreeSection_v
  exact LieHom.congr_fun h x

theorem zeroDegreeSection_map (x : ReducedGraded) :
    zeroDegreeSection (zeroDegreeMap x) = zeroProjectionHom x := by
  refine graded_induction (fun x => zeroDegreeSection (zeroDegreeMap x) = zeroProjectionHom x)
    ?_ ?_ ?_ x
  · simp only [map_zero]
  · intro a b ha hb
    simp only [map_add, ha, hb]
  · intro n a
    change zeroDegreeSection (zeroDegreeLinear (gradedClass n a)) = zeroProjection (gradedClass n a)
    cases n with
    | zero =>
      rw [zeroDegreeLinear_class_zero, zeroDegreeSection_evaluation, zeroProjection_class_zero]
      rfl
    | succ n =>
      rw [zeroDegreeLinear_class_of_ne _ (by omega), zeroProjection_class_of_ne _ (by omega), map_zero]

theorem zeroDegreeMap_ker : zeroDegreeMap.ker = positiveIdeal := by
  ext x
  change zeroDegreeMap x = 0 ↔ zeroProjectionHom x = 0
  constructor
  · intro h
    rw [← zeroDegreeSection_map, h, map_zero]
  · intro h
    have he := congrArg zeroDegreeMap h
    rw [← zeroDegreeSection_map, ← LieHom.comp_apply,
      zeroDegreeMap_section, LieHom.id_apply, map_zero] at he
    exact he

theorem zeroDegreeMap_apply_section (x : CrossProduct (ZMod 2)) :
    zeroDegreeMap (zeroDegreeSection x) = x := LieHom.congr_fun zeroDegreeMap_section x

theorem zeroDegreeMap_positive (x : positiveIdeal) : zeroDegreeMap x = 0 := by
  change (x : ReducedGraded) ∈ zeroDegreeMap.ker
  rw [zeroDegreeMap_ker]
  exact x.property

/-- The concrete splitting of the underlying vector space used for the
low-degree Chevalley--Eilenberg calculation. -/
def splitLinearEquiv : ReducedGraded ≃ₗ[ZMod 2] (CrossProduct (ZMod 2) × positiveIdeal) where
  toFun x := (zeroDegreeMap x, ⟨x - zeroDegreeSection (zeroDegreeMap x), by
    rw [zeroDegreeSection_map]
    exact sub_zeroProjection_mem x⟩)
  invFun p := zeroDegreeSection p.1 + (p.2 : ReducedGraded)
  left_inv x := by
    change zeroDegreeSection (zeroDegreeMap x) + (x - zeroDegreeSection (zeroDegreeMap x)) = x
    abel
  right_inv p := by
    apply Prod.ext
    · change zeroDegreeMap (zeroDegreeSection p.1 + (p.2 : ReducedGraded)) = p.1
      rw [map_add, zeroDegreeMap_apply_section, zeroDegreeMap_positive, add_zero]
    · apply Subtype.ext
      change zeroDegreeSection p.1 + (p.2 : ReducedGraded) -
        zeroDegreeSection (zeroDegreeMap (zeroDegreeSection p.1 + (p.2 : ReducedGraded))) = p.2
      rw [map_add, zeroDegreeMap_apply_section, zeroDegreeMap_positive, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add zeroDegreeMap x y
    · apply Subtype.ext
      change x + y - zeroDegreeSection (zeroDegreeMap (x + y)) =
        (x - zeroDegreeSection (zeroDegreeMap x)) + (y - zeroDegreeSection (zeroDegreeMap y))
      rw [map_add, map_add]
      abel
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul zeroDegreeMap c x
    · apply Subtype.ext
      change c • x - zeroDegreeSection (zeroDegreeMap (c • x)) =
        c • (x - zeroDegreeSection (zeroDegreeMap x))
      rw [map_smul, map_smul, smul_sub]

theorem splitLinearEquiv_symm_apply (p : CrossProduct (ZMod 2) × positiveIdeal) :
    splitLinearEquiv.symm p = zeroDegreeSection p.1 + (p.2 : ReducedGraded) := rfl

end Parafree.TheoremA.RationalModel
