/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Differentials.Polar
import Nyll.AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver

/-!
# Exists Unique has Simple Residue of has Simple Pole At
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs
namespace ExistsUnique_hasSimpleResidue_of_hasSimplePoleAt

open AlgebraicCurve

namespace ResEx

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem main [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (v : Place K F) (ω : Ω[F⁄K]) (hω : v.HasSimplePoleAt ω) :
    ∃! a : K, v.HasSimpleResidue ω a := by
  obtain ⟨f, hπf, hωf⟩ := hω
  have : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring ⟨v.uniformizer * f, hπf⟩)
  have hval : v.HasValue (v.uniformizer * f) a := ⟨hπf, ha.symm⟩
  refine ⟨a, ⟨f, hωf, hval⟩, ?_⟩
  intro b hb
  obtain ⟨f', hωf', hval'⟩ := hb
  have : v.DCoordGenerates := dCoordGenerates_of_isCurveOver v
  have hff : f' = f := by
    rw [← v.differentialCoeff_unique hωf', v.differentialCoeff_unique hωf]
  rw [hff] at hval'
  exact hval'.unique hval

end ResEx

theorem _root_.AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) (hω : v.HasSimplePoleAt ω) :
    ∃! a : K, v.HasSimpleResidue ω a :=
  ResEx.main v ω hω

end AlgebraicCurves.Differentials.Residues.Proofs.ExistsUnique_hasSimpleResidue_of_hasSimplePoleAt
end ProofImplementation
