/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_IsSmoothAt_flat_localization_atPrime.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Smooth.Flat

/-!
# Algebra Is Smooth At flat localization at Prime
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Algebra_IsSmoothAt_flat_localization_atPrime

open Algebra

theorem _root_.Algebra.IsSmoothAt.flat_localization_atPrime (R A : Type) [CommRing R] [CommRing A]
  [Algebra R A]
    [Algebra.FinitePresentation R A] (p : Ideal A) [p.IsPrime] [Algebra.IsSmoothAt R p] :
    Module.Flat R (Localization.AtPrime p) := by
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R p
  have := hsm
  have : Module.Flat R (Localization.Away f) := Algebra.Smooth.flat R _
  have hle : Submonoid.powers f ≤ p.primeCompl := by
    rintro x ⟨n, rfl⟩
    exact fun h => hf (‹p.IsPrime›.mem_of_pow_mem n h)
  let : Algebra (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f) p.primeCompl hle
  have : IsScalarTower A (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers f) p.primeCompl
      hle
  have : IsLocalization ((p.primeCompl).map (algebraMap A (Localization.Away f)))
    (Localization.AtPrime p) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers f) p.primeCompl hle
  have : Module.Flat (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) ((p.primeCompl).map (algebraMap A
      (Localization.Away f)))
  have : IsScalarTower R (Localization.Away f) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime p) r,
        IsScalarTower.algebraMap_apply R A (Localization.Away f) r,
        ← IsScalarTower.algebraMap_apply A (Localization.Away f) (Localization.AtPrime p)])
  exact Module.Flat.trans R (Localization.Away f) (Localization.AtPrime p)
end Algebra_IsSmoothAt_flat_localization_atPrime
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
