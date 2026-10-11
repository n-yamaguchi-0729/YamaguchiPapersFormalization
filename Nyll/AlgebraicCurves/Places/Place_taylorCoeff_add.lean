/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorCoeff_add.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Taylor
import Nyll.AlgebraicCurves.Places.EvaluationAlgebra
import Nyll.AlgebraicCurves.Places.Place_taylorRem_mem_toValuationSubring
import Nyll.AlgebraicCurves.Places.Place_taylorRem_add

/-!
# Place taylor Coeff add
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorCoeff_add

open AlgebraicCurve AlgebraicCurve.Place

namespace ProofAuxJetT4
open AlgebraicCurve AlgebraicCurve.Place
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_add_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_smul_of_mem (v : Place K F) (hv : v.IsRational) (c : K) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.evalAt (c • f) = c * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul_of_mem hv (v.algebraMap_mem' c) hf, v.evalAt_algebraMap_eq]

end ProofAuxJetT4

open ProofAuxJetT4 in
theorem _root_.AlgebraicCurve.Place.taylorCoeff_add
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (r : ℕ) :
    taylorCoeff v t r (f + g) = taylorCoeff v t r f + taylorCoeff v t r g := by
  rw [taylorCoeff_eq, taylorCoeff_eq, taylorCoeff_eq, taylorRem_add v hv ht hf hg r]
  exact evalAt_add_of_mem v hv (taylorRem_mem_toValuationSubring v hv ht hf r)
    (taylorRem_mem_toValuationSubring v hv ht hg r)
end AlgebraicCurves.Places.Proofs.Place_taylorCoeff_add
end ProofImplementation
