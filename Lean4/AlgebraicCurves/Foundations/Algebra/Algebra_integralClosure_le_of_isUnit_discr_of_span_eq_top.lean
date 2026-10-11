/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import AlgebraicCurves.Foundations.Algebra.Algebra_isIntegral_trace_of_finiteDimensional

/-!
# Algebra integral Closure le of is Unit discr of span eq top
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top

open Matrix
open scoped nonZeroDivisors

namespace IntegralClosureLeOfIsUnitDiscr
open _root_.Algebra

variable {R : Type*} [CommRing R] [IsDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

theorem isLocalization_of_span_eq_top (S : Subalgebra R A)
    (hS : Submodule.span K ((S : Subalgebra R A) : Set A) = ⊤) :
    IsLocalization (Algebra.algebraMapSubmonoid S R⁰) A := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, r, hr, rfl⟩
    have hr0 : (r : R) ≠ 0 := nonZeroDivisors.ne_zero hr
    have : algebraMap S A (algebraMap R S r) = algebraMap K A (algebraMap R K r) := by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [this]
    exact ((IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr hr0 |> isUnit_iff_ne_zero.mpr).map _
  · intro a
    have ha : a ∈ Submodule.span K ((S : Subalgebra R A) : Set A) :=
      by rw [hS]; exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha => exact ⟨⟨⟨a, ha⟩, 1⟩, by simp⟩
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | add a a' _ _ iha iha' =>
      obtain ⟨⟨s, m, hm⟩, h⟩ := iha
      obtain ⟨⟨s', m', hm'⟩, h'⟩ := iha'
      refine ⟨⟨m' * s + m * s', ⟨m * m', mul_mem hm hm'⟩⟩, ?_⟩
      simp only [map_mul, map_add] at h h' ⊢
      rw [← h, ← h']
      ring
    | smul k a _ iha =>
      obtain ⟨⟨s, m, hm⟩, h⟩ := iha
      obtain ⟨⟨n, d⟩, hk⟩ := IsLocalization.surj R⁰ k
      refine ⟨⟨algebraMap R S n * s, ⟨algebraMap R S d * m, mul_mem ⟨d, d.2, rfl⟩ hm⟩⟩, ?_⟩
      simp only at h ⊢
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply R S A, ←
        IsScalarTower.algebraMap_apply R S A,
        IsScalarTower.algebraMap_apply R K A, IsScalarTower.algebraMap_apply R K A,
        show k • a * (algebraMap K A (algebraMap R K d) * algebraMap S A m) =
          algebraMap K A (k * algebraMap R K d) * (a * algebraMap S A m) by
            rw [Algebra.smul_def, map_mul]; ring,
        hk, h]
  · intro a a' h
    exact ⟨1, by simpa using Subtype.val_injective h⟩

end IntegralClosureLeOfIsUnitDiscr

open IntegralClosureLeOfIsUnitDiscr in
theorem _root_.Algebra.integralClosure_le_of_isUnit_discr_of_span_eq_top
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [FiniteDimensional K
      A]
    (S : Subalgebra R A) (hS : Submodule.span K ((S : Subalgebra R A) : Set A) = ⊤)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (hdisc : IsUnit (Algebra.discr
      R b)) :
    integralClosure R A ≤ S := by
  classical
  intro x hx
  rw [mem_integralClosure_iff] at hx
  have : Module.Finite R S := Module.Finite.of_basis b
  have : Module.Free R S := Module.Free.of_basis b
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) A := isLocalization_of_span_eq_top
    S hS
  let bK : Module.Basis ι K A := b.localizationLocalization K R⁰ A
  have hbK : ∀ i, bK i = ((b i : S) : A) := fun i => Module.Basis.localizationLocalization_apply K
    R⁰ A b i
  have htr : ∀ j, ∃ r : R, algebraMap R K r = Algebra.trace K A (x * bK j) := by
    intro j
    refine IsIntegrallyClosed.isIntegral_iff.mp ?_
    refine Algebra.isIntegral_trace_of_finiteDimensional (hx.mul ?_)
    rw [hbK]
    exact (Algebra.IsIntegral.isIntegral (R := R) (b j)).map (IsScalarTower.toAlgHom R S A)
  choose t ht using htr
  set TR : Matrix ι ι R := Algebra.traceMatrix R b with hTRdef
  set TK : Matrix ι ι K := Algebra.traceMatrix K bK with hTKdef
  have hTK : TK = (algebraMap R K).mapMatrix TR := Algebra.traceMatrix_localizationLocalization R
    R⁰ A b
  have hdetR : IsUnit TR.det := by rwa [hTRdef, ← Algebra.discr_def]
  have hdetK : IsUnit TK.det := by
    rw [hTK, ← RingHom.map_det]
    exact hdetR.map _
  have hmul : TK *ᵥ (bK.equivFun x) = fun j => algebraMap R K (t j) := by
    rw [hTKdef, Algebra.traceMatrix_of_basis_mulVec]
    ext j
    exact (ht j).symm
  let cR : ι → R := TR⁻¹ *ᵥ t
  have hTc : TR *ᵥ cR = t := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetR, Matrix.one_mulVec]
  have hmap : TK *ᵥ (fun i => algebraMap R K (cR i)) = fun j => algebraMap R K (t j) := by
    rw [hTK, RingHom.mapMatrix_apply]
    ext j
    rw [show (fun i => algebraMap R K (cR i)) = algebraMap R K ∘ cR from rfl, ← RingHom.map_mulVec,
      hTc]
  have hcoord : bK.equivFun x = fun i => algebraMap R K (cR i) := by
    have h1 := congrArg (fun w => TK⁻¹ *ᵥ w) (hmul.trans hmap.symm)
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetK, Matrix.one_mulVec] using h1
  rw [← bK.sum_equivFun x, hcoord]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [hbK, algebraMap_smul, ← Subalgebra.coe_smul]
  exact (cR i • b i).2
end Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
