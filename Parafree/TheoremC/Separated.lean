import Parafree.TheoremC.Embedding
import Parafree.TheoremC.FirstLimit
import Parafree.Associative.FreeSeparation

/-! The full quotient is separated; the first limit is exactly the projection kernel. -/
noncomputable section
namespace Parafree.TheoremC
open Parafree.Associative Parafree.Associative.FreeAugmentation
variable (k : Type*) [CommRing k]

/-- The concrete embedding in equation (embedding), with augmentation-zero target letters. -/
def magnusEmbedding : A k →ₐ[k] FreeAlgebra k (Fin 4) :=
  (shiftEquiv k (Fin 4) (fun _ => 1)).toAlgHom.comp (Embedding.hom k)

theorem magnusEmbedding_injective : Function.Injective (magnusEmbedding k) :=
  (shiftEquiv k (Fin 4) (fun _ => 1)).injective.comp (Embedding.hom_injective k)

@[simp] theorem magnusEmbedding_augmentation_generator (i : Fin 6) :
    FreeAlgebra.algebraMapInv (magnusEmbedding k (generator k i)) = 0 := by
  change FreeAlgebra.algebraMapInv (shift k (Fin 4) (fun _ => 1)
    (Embedding.hom k (generator k i))) = 0
  rw [Embedding.hom_generator]
  fin_cases i <;> simp [Embedding.codeWord, WordKernel.code, word_cons, FreeAlgebra.algebraMapInv]

def augmentedMagnusEmbedding : AugmentedHom (augmentation k)
    (FreeAlgebra.algebraMapInv : FreeAlgebra k (Fin 4) →ₐ[k] k) where
  toAlgHom := magnusEmbedding k
  augmentation := by
    apply Ideal.Quotient.algHom_ext k
    apply FreeAlgebra.hom_ext
    funext i
    change FreeAlgebra.algebraMapInv (magnusEmbedding k (generator k i)) =
      augmentation k (generator k i)
    simp

theorem fullQuotient_residuallyNilpotent : ResiduallyNilpotent (augmentation k) :=
  (augmentedMagnusEmbedding k).residuallyNilpotent_of_injective
    (magnusEmbedding_injective k) (FreeAugmentation.residual_eq_bot k (Fin 4))

/-- The first limit, used in the transfinite calculation of Theorem D. -/
theorem firstLimit_eq_kernel : augmentationResidual (augmentation₀ k) = kernel k :=
  firstLimit_eq_kernel_of_separated k (fullQuotient_residuallyNilpotent k)

end Parafree.TheoremC
