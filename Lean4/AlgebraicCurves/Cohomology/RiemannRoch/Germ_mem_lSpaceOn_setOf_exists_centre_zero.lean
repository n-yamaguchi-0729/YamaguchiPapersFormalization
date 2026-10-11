/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_germ_mem_lSpaceOn_setOf_exists_centre_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Cech.DivisorSections
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-!
# Germ mem l Space On set Of exists centre zero
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Germ_mem_lSpaceOn_setOf_exists_centre_zero

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem _root_.AlgebraicCurve.germ_mem_lSpaceOn_setOf_exists_centre_zero
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] (U : C.Opens) (hU : genericPoint C ∈ U) (t : Γ(C, U)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    C.presheaf.germ U (genericPoint C) hU t ∈
      lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧
        (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 :
              Divisor k C.functionField) := by
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  change C.presheaf.germ U (genericPoint C) hU t ∈ lSpaceOn _ (0 : Divisor k C.functionField)
  rw [AlgebraicCurve.mem_lSpaceOn_iff]
  rintro v ⟨z, hzU, hz⟩
  have key : algebraMap (C.presheaf.stalk z) C.functionField (C.presheaf.germ U z hzU t) =
      C.presheaf.germ U (genericPoint C) hU t := by
    change (C.presheaf.germ U z hzU ≫ C.presheaf.stalkSpecializes ((genericPoint_spec
      C).specializes trivial)).hom t = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have h1 := (hz (C.presheaf.germ U z hzU t)).1
  rw [key] at h1
  simpa using h1
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Germ_mem_lSpaceOn_setOf_exists_centre_zero
end ProofImplementation
