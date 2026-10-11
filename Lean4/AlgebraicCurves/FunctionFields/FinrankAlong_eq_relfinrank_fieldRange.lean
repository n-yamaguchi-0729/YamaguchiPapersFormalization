/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import AlgebraicCurves.Divisors.Correspondences
import Mathlib.FieldTheory.Relrank

/-!
# Finrank Along eq relfinrank field Range
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.FinrankAlong_eq_relfinrank_fieldRange

theorem _root_.AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange {K E : Type*} [Field K] [Field
  E] [Algebra K E]
    (A B : IntermediateField K E) (phi : A →ₐ[K] B) :
    AlgebraicCurve.finrankAlong K phi =
      IntermediateField.relfinrank ((B.val.comp phi).fieldRange) B := by
  have hRange : (B.val.comp phi).fieldRange ≤ B := by
    rintro x ⟨a, rfl⟩
    exact (phi a).2
  rw [IntermediateField.relfinrank_eq_finrank_of_le hRange]
  let : Algebra A B := AlgebraicCurve.algebraAlong phi
  let sourceEquiv : A ≃+* ((B.val.comp phi).fieldRange) :=
    (AlgEquiv.ofInjectiveField (B.val.comp phi)).toRingEquiv
  let targetEquiv : B ≃+* (IntermediateField.extendScalars hRange) := RingEquiv.refl _
  exact Algebra.finrank_eq_of_equiv_equiv sourceEquiv targetEquiv (by
    refine RingHom.ext fun a => Subtype.ext ?_
    rfl)

end AlgebraicCurves.FunctionFields.Proofs.FinrankAlong_eq_relfinrank_fieldRange
end ProofImplementation
