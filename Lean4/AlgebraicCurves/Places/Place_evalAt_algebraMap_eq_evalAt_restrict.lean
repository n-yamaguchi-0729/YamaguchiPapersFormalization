/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Divisors.Maps

/-!
# Place eval At algebra Map eq eval At restrict
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_evalAt_algebraMap_eq_evalAt_restrict

open IsLocalRing AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap_eq_evalAt_restrict {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F') (hv : (w.restrict F).IsRational) {g : F} (hg : g ∈
  (w.restrict F).toValuationSubring) : w.evalAt (algebraMap F F' g) = (w.restrict F).evalAt g := by
  have hg' : algebraMap F F' g ∈ w.toValuationSubring := ValuationSubring.mem_comap.mp hg
  have h2 : residue w.toValuationSubring (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring)
      = algebraMap K w.ResidueField ((w.restrict F).evalAt g) := by
    have h3 : (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring)
        = restrictInclusion F w ⟨g, hg⟩ := rfl
    rw [h3, ← restrictResidueMap_residue, ((w.restrict F).algebraMap_evalAt hv hg).symm]
    change restrictResidueMap F w
        (residue _ (algebraMap K (w.restrict F).toValuationSubring ((w.restrict F).evalAt g)))
      = residue _ (algebraMap K w.toValuationSubring ((w.restrict F).evalAt g))
    rw [restrictResidueMap_residue]
    refine congrArg _ (Subtype.ext ?_)
    change algebraMap F F' (algebraMap K F ((w.restrict F).evalAt g))
        = algebraMap K F' ((w.restrict F).evalAt g)
    rw [← IsScalarTower.algebraMap_apply]
  rw [w.evalAt_of_mem hg', h2, w.residueInv_algebraMap]
end AlgebraicCurves.Places.Proofs.Place_evalAt_algebraMap_eq_evalAt_restrict
end ProofImplementation
