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

import SchemeTheory.Cohomology.Cech.TwoChartCech
import AlgebraicCurves.Cohomology.Sheaves.CoherentBaseChangeFamily
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_exists_fibreH0Family
import AlgebraicCurves.Cohomology.Cech.CoherentBaseChange_FibreH0Family_isClosed_setOf_le_h0
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
Closedness of the locus where a fibre kernel has dimension at least a fixed bound.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem _root_.TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (n : ℕ) :
    IsClosed {x : T | n ≤ Module.finrank (show PrimeSpectrum R from f.base x).asIdeal.ResidueField
      (LinearMap.ker (d.baseChange (show PrimeSpectrum R from f.base x).asIdeal.ResidueField))} :=
        by
  obtain ⟨F, hF⟩ := TwoChartCech.exists_fibreH0Family d f
  have : {x : T | n ≤ Module.finrank (show PrimeSpectrum R from f.base x).asIdeal.ResidueField
      (LinearMap.ker (d.baseChange (show PrimeSpectrum R from f.base x).asIdeal.ResidueField))} =
        {x : T | n ≤ F.h0 x} := by
    ext x; simp only [Set.mem_ofPred_eq, hF x]
  rw [this]
  exact F.isClosed_setOf_le_h0 n
end TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation

attribute [-simp] CoherentBaseChange.FibreH0Family.mk.sizeOf_spec
  CoherentBaseChange.FibreH0Family.mk.injEq
