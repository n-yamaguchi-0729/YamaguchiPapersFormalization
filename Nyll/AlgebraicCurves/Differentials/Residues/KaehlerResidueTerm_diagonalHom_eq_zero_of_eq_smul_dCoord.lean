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

import Nyll.AlgebraicCurves.Differentials.Residues.Basic

/-!
# Kaehler Residue Term diagonal Hom eq zero of eq smul d Coord
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs
namespace KaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord

open AlgebraicCurve

theorem _root_.AlgebraicCurve.kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
    {v : Place K F} [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : f ∈ v.toValuationSubring) (hω : ω = f • v.dCoord)
    {g : F} (hg : g ∈ v.toValuationSubring) :
    kaehlerResidueTerm ω (diagonalHom K F g) v = 0 := by
  unfold kaehlerResidueTerm
  rw [diagonalHom_apply, v.differentialCoeff_unique hω, v.localResidue_of_mem (mul_mem hg hf),
    map_zero]
end KaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord
end AlgebraicCurves.Differentials.Residues.Proofs
end ProofImplementation
