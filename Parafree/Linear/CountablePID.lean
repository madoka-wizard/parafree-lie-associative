import Mathlib.LinearAlgebra.FreeModule.PID

/-!
A basis for a submodule of a countably based free module over a PID.
The construction eliminates the last coordinate. It does not assume that the
submodule is finitely generated.
-/

noncomputable section

namespace Parafree.Linear.CountablePID

open Module

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

variable (N : Submodule R (ℕ →₀ R))

/-- Elements of the submodule supported strictly below `n`. -/
def stage (n : ℕ) : Submodule R N where
  carrier := {x | ∀ k, n ≤ k → (x : ℕ →₀ R) k = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy k hk
    simp [hx k hk, hy k hk]
  smul_mem' := by
    intro r x hx k hk
    simp [hx k hk]

def coordinate (n : ℕ) : N →ₗ[R] R :=
  (Finsupp.lapply n).comp N.subtype

/-- The ideal of possible last coordinates in the next finite stage. -/
def lastIdeal (n : ℕ) : Ideal R := (stage N (n + 1)).map (coordinate N n)

def diagonal (n : ℕ) : R := Submodule.IsPrincipal.generator (lastIdeal N n)

omit [IsDomain R] in
theorem exists_pivot (n : ℕ) :
    ∃ x : N, x ∈ stage N (n + 1) ∧ coordinate N n x = diagonal N n := by
  exact Submodule.mem_map.mp (Submodule.IsPrincipal.generator_mem (lastIdeal N n))

def pivot (n : ℕ) : N := (exists_pivot N n).choose

omit [IsDomain R] in
theorem pivot_stage (n : ℕ) : pivot N n ∈ stage N (n + 1) :=
  (exists_pivot N n).choose_spec.1

omit [IsDomain R] in
theorem pivot_coordinate (n : ℕ) : coordinate N n (pivot N n) = diagonal N n :=
  (exists_pivot N n).choose_spec.2

omit [IsDomain R] in
theorem pivot_above {i j : ℕ} (h : i < j) : coordinate N j (pivot N i) = 0 :=
  pivot_stage N i j h

/-- Only nonzero coordinate ideals contribute a basis vector. -/
abbrev Active := {n : ℕ // diagonal N n ≠ 0}

def vector (i : Active N) : N := pivot N i.val

theorem vectors_independent : LinearIndependent R (vector N) := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on_max with
  | empty => simp
  | @insert i s hmax ih =>
    intro g h j hj
    have hi : i ∉ s := fun hmem => (lt_irrefl i) (hmax i hmem)
    have hgi : g i = 0 := by
      have he := congrArg (coordinate N i.val) h
      rw [Finset.sum_insert hi, map_add, map_smul, map_sum, map_zero] at he
      have hzero : ∑ k ∈ s, coordinate N i.val (g k • vector N k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [map_smul, show coordinate N i.val (vector N k) = 0 from
          pivot_above N (hmax k hk), smul_zero]
      rw [hzero, add_zero, show coordinate N i.val (vector N i) = diagonal N i.val
        from pivot_coordinate N i.val, smul_eq_mul] at he
      exact (mul_eq_zero.mp he).resolve_right i.property
    have hs : ∑ k ∈ s, g k • vector N k = 0 := by
      simpa [Finset.sum_insert hi, hgi] using h
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hgi
    · exact ih g hs j hj

omit [IsDomain R] in
theorem stage_le_span (n : ℕ) :
    stage N n ≤ Submodule.span R (Set.range (vector N)) := by
  induction n with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by
      apply Subtype.ext
      ext k
      exact hx k (Nat.zero_le k)
    rw [hx0]
    exact Submodule.zero_mem _
  | succ n ih =>
    intro x hx
    have hxI : coordinate N n x ∈ lastIdeal N n :=
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ :=
      (Submodule.IsPrincipal.mem_iff_eq_smul_generator (lastIdeal N n)).mp hxI
    change coordinate N n x = r * diagonal N n at hr
    by_cases hd : diagonal N n = 0
    · apply ih
      intro k hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · change coordinate N n x = 0
        simp [hr, hd]
      · exact hx k hlt
    · have hprev : x - r • pivot N n ∈ stage N n := by
        intro k hk
        rcases Nat.eq_or_lt_of_le hk with rfl | hlt
        · change coordinate N n (x - r • pivot N n) = 0
          rw [map_sub, map_smul, pivot_coordinate, smul_eq_mul, hr, sub_self]
        · change (x : ℕ →₀ R) k - r • (pivot N n : ℕ →₀ R) k = 0
          rw [hx k hlt, pivot_stage N n k hlt, smul_zero, sub_self]
      have hv : pivot N n ∈ Submodule.span R (Set.range (vector N)) :=
        Submodule.subset_span ⟨⟨n, hd⟩, rfl⟩
      have := Submodule.add_mem _ (ih hprev) (Submodule.smul_mem _ r hv)
      simpa using this

omit [IsDomain R] in
theorem vectors_span : ⊤ ≤ Submodule.span R (Set.range (vector N)) := by
  classical
  intro x _
  apply stage_le_span N ((x : ℕ →₀ R).support.sup id + 1)
  intro k hk
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  have hle : k ≤ (x : ℕ →₀ R).support.sup id := Finset.le_sup (f := id) hmem
  omega

def basis : Basis (Active N) R N := Basis.mk (vectors_independent N) (vectors_span N)

theorem free : Module.Free R N := Module.Free.of_basis (basis N)

variable {M P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] {ι : Type*} [Countable ι]

/-- Freeness transfers through an injection into a module with a countable basis. -/
theorem free_of_injective (b : Basis ι R M) (f : P →ₗ[R] M)
    (hf : Function.Injective f) : Module.Free R P := by
  obtain ⟨e, he⟩ := exists_injective_nat ι
  let g : P →ₗ[R] (ℕ →₀ R) := (Finsupp.lmapDomain R R e).comp (b.repr.toLinearMap.comp f)
  have hg : Function.Injective g :=
    (Finsupp.mapDomain_injective he).comp (b.repr.injective.comp hf)
  letI : Module.Free R g.range := free g.range
  exact Module.Free.of_equiv (LinearEquiv.ofInjective g hg).symm

end Parafree.Linear.CountablePID
