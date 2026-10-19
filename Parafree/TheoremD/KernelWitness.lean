import Parafree.TheoremD.NormalBasis

/-! Powers of the first auxiliary letter are nonzero normal words. -/
noncomputable section
namespace Parafree.TheoremD.KernelWitness
open Parafree.TheoremC
open NormalWords NormalRepresentation NormalBasis
variable (k : Type*) [CommRing k]

/-- The first higher relator is the first auxiliary letter of the normal basis. -/
def z : A₀ k := toInitial k (relator k 2)

theorem z_mem_kernel : z k ∈ kernel k := full_relator k 2

theorem z_pow_ne_zero [Nontrivial k] (n : ℕ) : z k ^ n ≠ 0 := by
  have hn : Normal (List.replicate n (Z 0)) := by
    induction n with
    | zero => trivial
    | succ n ih => exact normal_prepend (by simp) ih
  have he : represent k (z k ^ n) = basis k ⟨List.replicate n (Z 0),hn⟩ := by
    simpa only [wordValue_replicate, value, z] using
      represent_wordValue k (List.replicate n (Z 0)) hn
  intro h
  rw [h, map_zero] at he
  have hc := congrArg (fun v : Space k => v ⟨List.replicate n (Z 0),hn⟩) he
  simp [basis] at hc

/-- No finite power of the kernel vanishes, including the zeroth power. -/
theorem kernel_pow_ne_bot [Nontrivial k] (n : ℕ) : kernel k ^ n ≠ ⊥ := by
  intro h
  have hz := Ideal.pow_mem_pow (z_mem_kernel k) n
  rw [h] at hz
  exact z_pow_ne_zero k n hz

end Parafree.TheoremD.KernelWitness
