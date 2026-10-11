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

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.FunctionFields.ConstantsAreBase_of_exists_isRational
import Nyll.AlgebraicCurves.Places.Place_isRational_iff_deg_eq_one

/-!
# ConstantsAreBase of deg eq one

A place of degree one identifies the constant field with the base field.
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.ConstantsAreBase_of_deg_eq_one

open AlgebraicCurve

theorem _root_.AlgebraicCurve.constantsAreBase_of_deg_eq_one {K F : Type*} [Field K] [Field F]
  [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (v₀ : AlgebraicCurve.Place K F) (hdeg : v₀.deg = 1) :
    AlgebraicCurve.ConstantsAreBase K F :=
  AlgebraicCurve.constantsAreBase_of_exists_isRational v₀ ((v₀.isRational_iff_deg_eq_one).mpr hdeg)
    (hdeg ▸ one_ne_zero)
end AlgebraicCurves.FunctionFields.Proofs.ConstantsAreBase_of_deg_eq_one
end ProofImplementation
