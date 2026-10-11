/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genus_eq_genusFF.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch
import Nyll.AlgebraicCurves.Cohomology.IndexOfSpecialty_eq_finrank_H1
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Ell_canonicalDivisor_eq_genus_of_riemannRoch

/-!
# Genus eq genus FF
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Genus_eq_genusFF

open AlgebraicCurve KaehlerDifferential

theorem _root_.AlgebraicCurve.genus_eq_genusFF
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F) (hWDA : AlgebraicCurve.WeilDualityAdelic K
      F)
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    AlgebraicCurve.genus K F = AlgebraicCurve.genusFF K F := by
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have h1 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (ell (canonicalDivisorOf hω - 0) : ℤ) :=
    hWDA hω 0
  rw [sub_zero] at h1
  have h2 : (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) :=
    ell_canonicalDivisor_eq_genus_of_riemannRoch hRR hC hω
  have h3 : indexOfSpecialty (0 : Divisor K F) = Module.finrank K (H1 (0 : Divisor K F)) :=
    indexOfSpecialty_eq_finrank_H1 0
  have h4 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (genusFF K F : ℤ) := by
    rw [genusFF, ← h3]
  have : (genus K F : ℤ) = (genusFF K F : ℤ) := by
    rw [← h4, h1, h2]
  exact_mod_cast this
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Genus_eq_genusFF
end ProofImplementation
