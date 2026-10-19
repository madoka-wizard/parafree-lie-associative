import Parafree.TheoremD.KernelBasis

/-! Separation of kernel powers from the normal-word coordinates. -/
noncomputable section
namespace Parafree.TheoremD.KernelSeparation
open Parafree.TheoremC
open NormalWords NormalBasis NormalFiltration
variable (k : Type*) [CommRing k]

/-- Each coefficient vanishes by looking one stage beyond its number of
auxiliary letters. Hence the intersection of all kernel powers is zero. -/
theorem kernel_iInf_pow_eq_bot : (⨅ n : ℕ, kernel k ^ n) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply (equiv k).symm.injective
  change represent k x = represent k 0
  rw [map_zero]
  ext w
  have hw := (Submodule.mem_iInf (fun n : ℕ => kernel k ^ n)).mp hx (countZ w.val+1)
  exact (mem_level_iff k _ _).mp ((KernelBasis.mem_kernel_power_iff k _ x).mp hw)
    w (Nat.lt_succ_self _)

end Parafree.TheoremD.KernelSeparation
