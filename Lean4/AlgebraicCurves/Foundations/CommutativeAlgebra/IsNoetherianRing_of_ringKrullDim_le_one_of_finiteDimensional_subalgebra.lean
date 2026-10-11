/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Defs
import AlgebraicCurves.Foundations.CommutativeAlgebra.Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite

/-!
# Noetherian subalgebras of finite fraction-field extensions

Subalgebras of finite-dimensional fraction-field extensions of Noetherian
domains of Krull dimension at most one are Noetherian and have Krull
dimension at most one.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra

universe u v w

theorem _root_.IsNoetherianRing.of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (B : Subalgebra R L) :
    IsNoetherianRing ↥B ∧ ringKrullDim ↥B ≤ 1 := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hR
  obtain ⟨hN, hD, -⟩ :=
    Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite (K := K) B
  have := hD
  exact ⟨hN, Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ↥B)⟩
end IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
