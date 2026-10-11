/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_LinearMap_isOpen_setOf_surjective_baseChange_residueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Tactic.Ext

/-!
The locus where a linear map is surjective after residue-field base change is open.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace LinearMap_isOpen_setOf_surjective_baseChange_residueField

universe u v w

open TensorProduct

theorem _root_.LinearMap.isOpen_setOf_surjective_baseChange_residueField
    {A : Type u} [CommRing A] {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P]
      [AddCommGroup Q] [Module A Q]
    (d : P →ₗ[A] Q) [Module.Finite A (Q ⧸ LinearMap.range d)] :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)} :=
  by
  have key : ∀ (K : Type u) [CommRing K] [Algebra A K],
      Function.Surjective (d.baseChange K) ↔ Subsingleton (K ⊗[A] (Q ⧸ LinearMap.range d)) := by
    intro K _ _
    rw [(TensorProduct.tensorQuotientEquiv K (LinearMap.range d)).toEquiv.subsingleton_congr,
      Submodule.Quotient.subsingleton_iff, LinearMap.baseChange_eq_ltensor, ←
        LinearMap.range_eq_top]
    have : (TensorProduct.map LinearMap.id (LinearMap.range d).subtype).range =
      (LinearMap.lTensor K d).range :=
      (LinearMap.lTensor_range K).symm
    rw [this]
  have h : {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)} =
      (Module.support A (Q ⧸ LinearMap.range d))ᶜ := by
    ext 𝔭
    rw [Set.mem_ofPred_eq, key, Set.mem_compl_iff,
      Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
  rw [h]
  exact Module.isClosed_support.isOpen_compl
end LinearMap_isOpen_setOf_surjective_baseChange_residueField
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
