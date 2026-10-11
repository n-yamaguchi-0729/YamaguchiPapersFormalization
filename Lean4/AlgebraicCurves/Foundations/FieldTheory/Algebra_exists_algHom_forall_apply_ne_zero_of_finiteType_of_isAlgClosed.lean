/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Algebra exists alg Hom forall apply ne zero of finite Type of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.FieldTheory.Proofs
namespace Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed

theorem _root_.Algebra.exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
    {k : Type*} [Field k] [IsAlgClosed k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    {ι : Type*} [Finite ι] (g : ι → B) (hg : ∀ i, g i ≠ 0) :
    ∃ χ : B →ₐ[k] k, ∀ i, χ (g i) ≠ 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set G : B := ∏ i, g i with hGdef
  have hG : G ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hg i)
  let S := Localization.Away G
  have : Nontrivial S := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have hinj : Function.Injective (algebraMap B S) :=
      IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hG)
    exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact h))
  have : Algebra.FiniteType k S := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  have := hm
  let : Field (S ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (S ⧸ m) := Algebra.FiniteType.trans (S := S) inferInstance
    inferInstance
  have : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  have : Algebra.IsAlgebraic k (S ⧸ m) := Algebra.IsAlgebraic.of_finite k (S ⧸ m)
  let φ : (S ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  let ψ : B →ₐ[k] S ⧸ m := (Ideal.Quotient.mkₐ k m).comp (IsScalarTower.toAlgHom k B S)
  refine ⟨φ.comp ψ, fun i => ?_⟩
  have hGunit : IsUnit (algebraMap B S G) := IsLocalization.Away.algebraMap_isUnit G
  have hGS : (φ.comp ψ) G ≠ 0 := by
    intro h0
    have hu : IsUnit ((φ.comp ψ) G) := by
      have : (φ.comp ψ) G = φ (Ideal.Quotient.mk m (algebraMap B S G)) := rfl
      rw [this]
      exact (hGunit.map (Ideal.Quotient.mk m)).map φ
    exact hu.ne_zero h0
  intro hgi
  apply hGS
  change (φ.comp ψ) (∏ i, g i) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hgi

end Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
end AlgebraicCurves.Foundations.FieldTheory.Proofs
end ProofImplementation
