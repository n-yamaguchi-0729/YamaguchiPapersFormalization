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

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Places.Rational.Basic
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.Differentials.Uniformizer
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Differentials.Kaehler.Weil
import AlgebraicCurves.Differentials.Residues.ResidueTheoremK_of_isAlgClosed
import AlgebraicCurves.Differentials.Residues.ResidueTheorem_of_residueTheoremK

/-!
# Residue Theorem of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheorem_of_isAlgClosed


open AlgebraicCurve

theorem _root_.AlgebraicCurve.residueTheorem_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    (hcurve : AlgebraicCurve.IsCurveOver K F)
    [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    ∀ [AlgebraicCurve.HasPrincipalDivisors K F], AlgebraicCurve.ResidueTheorem K F := by
  classical
  have hK : AlgebraicCurve.ResidueTheoremK K F := by
    let _ : AlgebraicCurve.IsCurveOver K F := hcurve
    exact residueTheoremK_of_isAlgClosed (K := K) (F := F)
  intro _hPD ω hω f
  exact residueTheorem_of_residueTheoremK (K := K) (F := F) hK hω f
end AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheorem_of_isAlgClosed
end ProofImplementation
