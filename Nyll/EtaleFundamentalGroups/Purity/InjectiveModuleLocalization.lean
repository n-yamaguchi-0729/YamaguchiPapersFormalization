/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Localization of an injective module

Over a Noetherian ring the localization map of an injective module is
surjective. Stabilization of the kernels of powers of a denominator makes
an appropriate division map well-defined on a principal ideal; injectivity
extends that map to the ring. For a principal localization the kernel is
exactly the principal ideal-power torsion submodule.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]
variable (E : Type u) [AddCommGroup E] [Module R E]

/-- Localization of an injective module over a Noetherian ring is a quotient
of the original module. -/
theorem localizedModule_mkLinearMap_surjective_of_injective
    [IsNoetherianRing R] [Module.Injective R E] (S : Submonoid R) :
    Function.Surjective (LocalizedModule.mkLinearMap S E) := by
  intro z
  obtain ⟨⟨y, s⟩, rfl⟩ :=
    IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S E) z
  change ∃ a, LocalizedModule.mkLinearMap S E a =
    IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S E) y s
  rw [← IsLocalizedModule.mk_eq_mk']
  let e : Module.End R R := LinearMap.lsmul R R (s : R)
  have he (n : ℕ) (a : R) : (e ^ n) a = (s : R) ^ n * a := by
    induction n generalizing a with
    | zero => simp only [pow_zero, Module.End.one_apply, one_mul]
    | succ n hn =>
      rw [pow_succ, Module.End.mul_apply, hn, pow_succ]
      change (s : R) ^ n * ((s : R) * a) = _
      exact (mul_assoc _ _ _).symm
  obtain ⟨n, hn : ∀ m, n ≤ m →
      LinearMap.ker (e ^ n) = LinearMap.ker (e ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr
      (inferInstance : IsNoetherian R R) e.iterateKer
  have hker : LinearMap.ker (e ^ (n + 1)) ≤ LinearMap.ker (e ^ n) := by
    rw [hn (n + 1) (Nat.le_succ n)]
  let v : R →ₗ[R] E := (LinearMap.toSpanSingleton R E y).comp (e ^ n)
  have hkv : LinearMap.ker (e ^ (n + 1)) ≤ LinearMap.ker v := by
    intro a ha
    change (e ^ n) a • y = 0
    rw [show (e ^ n) a = 0 from hker ha, zero_smul]
  let q : LinearMap.range (e ^ (n + 1)) →ₗ[R] E :=
    ((LinearMap.ker (e ^ (n + 1))).liftQ v hkv).comp
      (e ^ (n + 1)).quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R E
    (LinearMap.range (e ^ (n + 1))) R
    (LinearMap.range (e ^ (n + 1))).subtype Subtype.val_injective q
  have hdivide : (s : R) ^ (n + 1) • g 1 = (s : R) ^ n • y := by
    have hmem : (e ^ (n + 1)) 1 ∈ LinearMap.range (e ^ (n + 1)) :=
      LinearMap.mem_range_self (e ^ (n + 1)) 1
    have h := LinearMap.congr_fun hg
      ⟨(e ^ (n + 1)) 1, hmem⟩
    change g ((e ^ (n + 1)) 1) = q ⟨(e ^ (n + 1)) 1, hmem⟩ at h
    change g ((e ^ (n + 1)) 1) =
      (LinearMap.ker (e ^ (n + 1))).liftQ v hkv
        ((e ^ (n + 1)).quotKerEquivRange.symm
          ⟨(e ^ (n + 1)) 1, hmem⟩) at h
    have hquot := LinearMap.quotKerEquivRange_symm_apply_image
      (e ^ (n + 1)) 1 hmem
    rw [hquot] at h
    change g ((e ^ (n + 1)) 1) = (e ^ n) 1 • y at h
    rw [he, he, mul_one, mul_one] at h
    calc
      (s : R) ^ (n + 1) • g 1 = g ((s : R) ^ (n + 1) • (1 : R)) :=
        (g.map_smul _ _).symm
      _ = g ((s : R) ^ (n + 1)) := by rw [smul_eq_mul, mul_one]
      _ = (s : R) ^ n • y := h
  refine ⟨g 1, ?_⟩
  apply LocalizedModule.mk_eq.mpr
  refine ⟨s ^ n, ?_⟩
  change (s : R) ^ n • ((s : R) • g 1) = (s : R) ^ n • ((1 : R) • y)
  rw [one_smul, ← mul_smul, ← pow_succ]
  exact hdivide

/-- The kernel of principal localization is principal ideal-power torsion. -/
theorem ker_localizedModule_mkLinearMap_powers (x : R) :
    LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers x) E) =
      Ideal.primaryComponent E (Ideal.span {x}) := by
  ext y
  rw [LocalizedModule.mem_ker_mkLinearMap_iff, Ideal.primaryComponent_mem]
  constructor
  · rintro ⟨a, ⟨n, rfl⟩, hy⟩
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro b
    have hb : (b : R) ∈ Ideal.span {x ^ n} := by
      rw [← Ideal.span_singleton_pow]
      exact b.property
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hb
    rw [← hc, mul_smul, hy, smul_zero]
  · rintro ⟨n, hn⟩
    refine ⟨x ^ n, ⟨n, rfl⟩, ?_⟩
    exact (Submodule.mem_torsionBySet_iff
      (((Ideal.span {x}) ^ n : Ideal R) : Set R) y).mp hn
      ⟨x ^ n, by
        rw [Ideal.span_singleton_pow]
        exact Ideal.mem_span_singleton_self (x ^ n)⟩

end EtaleFundamentalGroups.Purity
