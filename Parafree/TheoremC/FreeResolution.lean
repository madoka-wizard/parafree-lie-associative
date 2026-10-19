import Parafree.TheoremC.PresentationComplex
import Parafree.Associative.DerivedCoinvariants
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! A free resolution of length two for the infinitely presented algebra A. -/
noncomputable section
namespace Parafree.TheoremC.FreeResolution
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category PresentationComplex
open Parafree.Associative
open scoped ZeroObject
universe u
variable (k : Type u) [CommRing k]

def objects : ℕ → ModuleCat.{u} (A k)
  | 0 => ModuleCat.of (A k) (A k)
  | 1 => ModuleCat.of (A k) (P₁ k)
  | 2 => ModuleCat.of (A k) (P₂ k)
  | _+3 => 0

def differential : ∀ n, objects k (n+1) ⟶ objects k n
  | 0 => ModuleCat.ofHom (d₁ k)
  | 1 => ModuleCat.ofHom (d₂ k)
  | _+2 => 0

theorem differential_sq (n : ℕ) : differential k (n+1) ≫ differential k n = 0 := by
  obtain (_ | _ | n) := n
  · apply ModuleCat.hom_ext
    exact d₁_d₂ k
  · exact zero_comp
  · exact zero_comp

def complex : ChainComplex (ModuleCat.{u} (A k)) ℕ :=
  ChainComplex.of (objects k) (differential k) (differential_sq k)

instance complex_projective (n : ℕ) : Projective ((complex k).X n) := by
  obtain (_ | _ | _ | n) := n <;> dsimp [complex, ChainComplex.of, objects] <;> infer_instance

theorem exactAt_succ (n : ℕ) : (complex k).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  change (ShortComplex.mk _ _ ((complex k).d_comp_d (n+2) (n+1) n)).Exact
  simp only [complex, ChainComplex.of_d]
  obtain (_ | _ | n) := n
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (exact_d₂_d₁ k)
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    have hz : x = 0 := d₂_injective k (hx.trans (map_zero (d₂ k)).symm)
    exact ⟨0, by change (0 : P₂ k) = x; exact hz.symm⟩
  · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero _)

def trivialModule : ModuleCat.{u} (A k) := ModuleCat.of (A k) (A k ⧸ augmentationIdeal (augmentation k))

theorem d₁_q : ModuleCat.ofHom (d₁ k) ≫ ModuleCat.ofHom (q k) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact (exact_d₁_q k _).mpr ⟨v,rfl⟩

instance q_epi : Epi (ModuleCat.ofHom (q k)) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentationIdeal (augmentation k)).mkQ_surjective

def π : complex k ⟶ (ChainComplex.single₀ (ModuleCat.{u} (A k))).obj (trivialModule k) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (q k), by
    simpa only [complex, ChainComplex.of_d, differential] using d₁_q k⟩

set_option backward.isDefEq.respectTransparency false in
theorem π_quasiIso : QuasiIso (π k) := ⟨fun n => by
  cases n
  · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · dsimp [π]
      refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
        ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
          (ShortComplex.mk _ _ (d₁_q k))).mpr (exact_d₁_q k), q_epi k⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [complex, ChainComplex.of, differential]) (by simp)
    all_goals rfl
  · rw [quasiIsoAt_iff_exactAt']
    · apply exactAt_succ
    · apply ChainComplex.exactAt_succ_single_obj⟩

/-- A genuine projective resolution, carrying the quasi-isomorphism to the
trivial module. All positive degrees above two are zero. -/
def resolution : ProjectiveResolution (trivialModule k) where
  complex := complex k
  π := π k
  quasiIso := π_quasiIso k

end Parafree.TheoremC.FreeResolution
