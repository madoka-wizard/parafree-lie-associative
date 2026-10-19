import Parafree.Associative.FreeAugmentation

/-! Word evaluation and translation of free generators. -/
noncomputable section
namespace Parafree.Associative.FreeAugmentation
variable (R X : Type*) [CommRing R]

theorem word_append (v w : List X) : word R X (v ++ w) = word R X v * word R X w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w x ih =>
    rw [← List.append_assoc, word_concat, ih, word_concat, mul_assoc]

theorem word_singleton (x : X) : word R X [x] = FreeAlgebra.ι R x := by
  simpa using word_concat R X [] x

theorem word_cons (x : X) (w : List X) : word R X (x :: w) = FreeAlgebra.ι R x * word R X w := by
  simpa only [word_singleton] using word_append R X [x] w

theorem map_word {B : Type*} [Ring B] [_root_.Algebra R B] (f : FreeAlgebra R X →ₐ[R] B) (w : List X) :
    f (word R X w) = (w.map (fun x => f (FreeAlgebra.ι R x))).prod := by
  induction w with
  | nil => simp
  | cons x w ih => simp [word_cons, ih]

def shift (c : X → R) : FreeAlgebra R X →ₐ[R] FreeAlgebra R X :=
  FreeAlgebra.lift R (fun x => FreeAlgebra.ι R x + algebraMap R _ (c x))

@[simp] theorem shift_ι (c : X → R) (x : X) :
    shift R X c (FreeAlgebra.ι R x) = FreeAlgebra.ι R x + algebraMap R _ (c x) :=
  FreeAlgebra.lift_ι_apply _ _

theorem shift_neg_comp (c : X → R) :
    (shift R X (-c)).comp (shift R X c) = AlgHom.id R _ := by
  apply FreeAlgebra.hom_ext
  funext x
  simp

def shiftEquiv (c : X → R) : FreeAlgebra R X ≃ₐ[R] FreeAlgebra R X :=
  AlgEquiv.ofAlgHom (shift R X c) (shift R X (-c))
    (by simpa using shift_neg_comp R X (-c)) (shift_neg_comp R X c)

@[simp] theorem shiftEquiv_apply (c : X → R) (x : FreeAlgebra R X) :
    shiftEquiv R X c x = shift R X c x := rfl

end Parafree.Associative.FreeAugmentation
