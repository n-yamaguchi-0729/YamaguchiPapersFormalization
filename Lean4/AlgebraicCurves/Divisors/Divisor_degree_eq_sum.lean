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

import AlgebraicCurves.Divisors.ClassGroup

/-!
Compute the degree of a divisor as a sum of weighted coefficients.
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_degree_eq_sum

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

end

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Divisor.degree_eq_sum {K F : Type*} [Field K] [Field F] [Algebra K
    F] (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
  Finsupp.liftAddHom_apply (fun v : Place K F => AddMonoidHom.mulRight (v.deg : ℤ)) D
end AlgebraicCurves.Divisors.Proofs.Divisor_degree_eq_sum
end ProofImplementation
