/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Empty
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Secondary decompositions of Artinian modules

Multiplication on a secondary module is either surjective or nilpotent.
If an Artinian module fails this condition, the stabilized kernel-range
sum for the offending multiplication expresses it as the sum of two
proper submodules.  Well-founded induction on submodules therefore gives
a finite secondary decomposition.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A nonzero module is secondary when every scalar acts surjectively or
some power of that scalar annihilates the whole module. -/
def IsSecondaryModule (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧
    ∀ r : R,
      Function.Surjective (fun x : M ↦ r • x) ∨
        ∃ n : ℕ, ∀ x : M, r ^ n • x = 0

/-- If an endomorphism of an Artinian module is neither surjective nor
nilpotent, a kernel and range of the same power are proper and sum to the
whole module.  No Noetherian hypothesis is needed for this sum. -/
theorem exists_ker_pow_lt_top_range_pow_lt_top
    [IsArtinian R M] (f : Module.End R M)
    (hsurj : ¬ Function.Surjective f) (hnil : ¬ IsNilpotent f) :
    ∃ n : ℕ,
      LinearMap.ker (f ^ n) < ⊤ ∧
        LinearMap.range (f ^ n) < ⊤ ∧
          LinearMap.ker (f ^ n) ⊔ LinearMap.range (f ^ n) = ⊤ := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    (LinearMap.eventually_codisjoint_ker_pow_range_pow f)
  refine ⟨n + 1, ?_, ?_, codisjoint_iff.mp (hn (n + 1) (Nat.le_succ n))⟩
  · apply lt_top_iff_ne_top.mpr
    intro hker
    exact hnil ⟨n + 1, LinearMap.ker_eq_top.mp hker⟩
  · apply lt_top_iff_ne_top.mpr
    intro hrange
    have hpow : Function.Surjective (f ^ (n + 1)) :=
      LinearMap.range_eq_top.mp hrange
    apply hsurj
    intro y
    obtain ⟨x, hx⟩ := hpow y
    refine ⟨(f ^ n) x, ?_⟩
    simpa only [pow_succ', Module.End.mul_apply] using hx

/-- Every Artinian module is the sum of finitely many nonzero secondary
submodules; the zero module has the empty decomposition. -/
theorem exists_finset_secondarySubmodules_sup_eq_top [IsArtinian R M] :
    ∃ s : Finset (Submodule R M),
      (∀ N ∈ s, IsSecondaryModule R N) ∧ s.sup id = ⊤ := by
  classical
  refine IsArtinian.induction
    (P := fun N : Submodule R M ↦
      ∃ s : Finset (Submodule R M),
        (∀ Q ∈ s, IsSecondaryModule R Q) ∧ s.sup id = N) ?_ ⊤
  intro N ih
  by_cases hN : N = ⊥
  · refine ⟨∅, ?_, ?_⟩
    · intro Q hQ
      exact False.elim (Finset.notMem_empty Q hQ)
    · simpa only [Finset.sup_empty] using hN.symm
  by_cases hsecondary : IsSecondaryModule R N
  · refine ⟨{N}, ?_, ?_⟩
    · intro Q hQ
      have hQN : Q = N := Finset.mem_singleton.mp hQ
      exact hQN.symm ▸ hsecondary
    · exact Finset.sup_singleton
  let : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  have hfail : ¬ ∀ r : R,
      Function.Surjective (fun x : N ↦ r • x) ∨
        ∃ n : ℕ, ∀ x : N, r ^ n • x = 0 := by
    intro h
    exact hsecondary ⟨inferInstance, h⟩
  obtain ⟨r, hr⟩ := not_forall.mp hfail
  obtain ⟨hrsurj, hrnil⟩ := not_or.mp hr
  let f : Module.End R N := r • (LinearMap.id : N →ₗ[R] N)
  have hpow : ∀ (n : ℕ) (x : N), (f ^ n) x = r ^ n • x := by
    intro n
    induction n with
    | zero =>
        intro x
        simp only [pow_zero, Module.End.one_apply, one_smul]
    | succ n ihpow =>
        intro x
        calc
          (f ^ (n + 1)) x = f ((f ^ n) x) := by
            rw [pow_succ', Module.End.mul_apply]
          _ = r • (r ^ n • x) := by
            change r • ((f ^ n) x) = r • (r ^ n • x)
            exact congrArg (fun z : N ↦ r • z) (ihpow x)
          _ = r ^ (n + 1) • x := by
            rw [pow_succ', mul_smul]
  have hfsurj : ¬ Function.Surjective f := by
    intro hf
    apply hrsurj
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨x, hx⟩
  have hfnil : ¬ IsNilpotent f := by
    rintro ⟨n, hn⟩
    apply hrnil
    refine ⟨n, ?_⟩
    intro x
    rw [← hpow n x, hn, LinearMap.zero_apply]
  obtain ⟨n, hker, hrange, hsum⟩ :=
    exists_ker_pow_lt_top_range_pow_lt_top f hfsurj hfnil
  let K : Submodule R M := (LinearMap.ker (f ^ n)).map N.subtype
  let L : Submodule R M := (LinearMap.range (f ^ n)).map N.subtype
  have hK : K < N := by
    have h := (Submodule.map_strictMono_of_injective N.subtype_injective) hker
    simpa only [Submodule.map_top, Submodule.range_subtype] using h
  have hL : L < N := by
    have h := (Submodule.map_strictMono_of_injective N.subtype_injective) hrange
    simpa only [Submodule.map_top, Submodule.range_subtype] using h
  have hKL : K ⊔ L = N := by
    change (LinearMap.ker (f ^ n)).map N.subtype ⊔
      (LinearMap.range (f ^ n)).map N.subtype = N
    rw [← Submodule.map_sup, hsum, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨s, hs, hsup_s⟩ := ih K hK
  obtain ⟨t, ht, hsup_t⟩ := ih L hL
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro Q hQ
    obtain hQs | hQt := Finset.mem_union.mp hQ
    · exact hs Q hQs
    · exact ht Q hQt
  · rw [Finset.sup_union, hsup_s, hsup_t, hKL]

end EtaleFundamentalGroups.Purity
