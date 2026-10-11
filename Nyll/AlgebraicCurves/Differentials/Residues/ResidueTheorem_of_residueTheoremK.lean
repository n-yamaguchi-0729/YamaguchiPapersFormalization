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

import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil

/-!
Transfer the residue theorem from its base-field formulation.
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheorem_of_residueTheoremK


open AlgebraicCurve

theorem _root_.AlgebraicCurve.residueTheorem_of_residueTheoremK
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (h : AlgebraicCurve.ResidueTheoremK K F) :
    ∀ [AlgebraicCurve.HasPrincipalDivisors K F], AlgebraicCurve.ResidueTheorem K F := by
  intro _hPD ω hω f
  have key := h (fun v => HasCanonicalLocalResidueKStar.dataKStar v) hω f
  rw [weilOfKaehlerK_apply] at key
  rw [weilOfKaehler_apply]
  exact key
end AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheorem_of_residueTheoremK
end ProofImplementation
