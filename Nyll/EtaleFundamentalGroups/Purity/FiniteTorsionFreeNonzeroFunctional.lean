/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Nonzero functionals on finite torsion-free modules

Localizing a torsion-free module in the fraction field preserves its
nonzero vectors. A vector-space functional separates such a vector;
clearing the denominators of finitely many generators gives a functional
with values in the original domain.
-/

namespace EtaleFundamentalGroups.Purity

open nonZeroDivisors

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.IsTorsionFree R M]

/-- A nonzero vector in a finite torsion-free module is detected by an
`R`-valued linear functional. -/
theorem exists_linearMap_apply_ne_zero_of_finite_torsionFree
    (z : M) (hz : z ≠ 0) : ∃ f : M →ₗ[R] R, f z ≠ 0 := by
  classical
  let V := LocalizedModule R⁰ M
  let loc : M →ₗ[R] V := LocalizedModule.mkLinearMap R⁰ M
  have hloc : Function.Injective loc := by
    apply (IsLocalizedModule.injective_iff_isRegular R⁰ loc).2
    intro c
    exact IsSMulRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero c)
  have hlocz : loc z ≠ 0 := by
    intro h
    exact hz (hloc (h.trans (map_zero loc).symm))
  let : IsScalarTower R (FractionRing R) V :=
    IsScalarTower.of_algebraMap_smul fun a w => by
      induction w using LocalizedModule.induction_on with
      | h m s =>
        rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk,
          one_mul, LocalizedModule.smul'_mk]
  obtain ⟨g, hgz, _⟩ := Submodule.exists_le_ker_of_notMem
    (p := (⊥ : Submodule (FractionRing R) V))
    (v := loc z) (show loc z ∉ (⊥ : Submodule (FractionRing R) V) from hlocz)
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite R⁰
    (fun j : Fin n => g (loc (s j)))
  let h : M →ₗ[R] FractionRing R :=
    (c : R) • ((g.restrictScalars R).comp loc)
  let alg : R →ₗ[R] FractionRing R := Algebra.linearMap R (FractionRing R)
  have hspan : (⊤ : Submodule R M) ≤ (LinearMap.range alg).comap h := by
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro w ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := hc j
    exact ⟨a, ha⟩
  have hall : ∀ w : M, h w ∈ LinearMap.range alg :=
    fun w => hspan (Submodule.mem_top : w ∈ (⊤ : Submodule R M))
  let e : R ≃ₗ[R] LinearMap.range alg :=
    LinearEquiv.ofInjective alg (IsFractionRing.injective R (FractionRing R))
  let f : M →ₗ[R] R :=
    e.symm.toLinearMap.comp (h.codRestrict (LinearMap.range alg) hall)
  have hf : alg (f z) = h z :=
    LinearEquiv.ofInjective_symm_apply alg
      (h := IsFractionRing.injective R (FractionRing R)) ⟨h z, hall z⟩
  refine ⟨f, ?_⟩
  intro hfz
  have hhz : h z = 0 := by rw [← hf, hfz, map_zero]
  have hcz : c • g (loc z) = c • (0 : FractionRing R) := by
    change (c : R) • g (loc z) = (c : R) • (0 : FractionRing R)
    rw [smul_zero]
    exact hhz
  exact hgz ((IsLocalization.smul_bijective (FractionRing R) c).injective hcz)

/-- A finite nonzero torsion-free module over a domain has a nonzero
linear functional into the domain. -/
theorem exists_ne_zero_linearMap_of_finite_torsionFree [Nontrivial M] :
    ∃ f : M →ₗ[R] R, f ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_ne (0 : M)
  obtain ⟨f, hf⟩ := exists_linearMap_apply_ne_zero_of_finite_torsionFree (R := R) z hz
  refine ⟨f, ?_⟩
  intro h
  apply hf
  rw [h]
  rfl

end EtaleFundamentalGroups.Purity
