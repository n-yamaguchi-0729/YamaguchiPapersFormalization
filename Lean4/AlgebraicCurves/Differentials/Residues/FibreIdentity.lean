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

import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.Cohomology.Cech.Maps

/-!
# Differentials, residues, and divisor correspondences

The compatibility of residue sums over a place fibre with differential pullback and field trace.
-/

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

/-- For each base place, the sum of pulled-back differential residues over its fibre equals
the residue of the traced function. -/
def FibreResidueIdentityAlong [HasPrincipalDivisors K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) : Prop :=
  ∀ (v : Place K F) (ω : Ω[F⁄K]) (f' : F'),
    ∑ w ∈ Place.fiberAlong φ hφ v,
        kaehlerResidueTerm (Differential.pullbackAlong φ ω) (diagonalHom K F' f') w
      = kaehlerResidueTerm ω (diagonalHom K F (traceFunAlong φ f')) v

end AlgebraicCurve

end
