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

import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.Places.Place_exists_restrict_eq

/-!
# Rational Function Field nonempty place of rat Func tower
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFieldPlaceRatFuncTower

open AlgebraicCurve

theorem _root_.AlgebraicCurve.RationalFunctionField.nonempty_place_of_ratFunc_tower (K : Type*)
  [Field K]
    (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable
      (RatFunc K) F] :
    Nonempty (AlgebraicCurve.Place K F) := open scoped Classical in
  (AlgebraicCurve.Place.exists_restrict_eq (M := F)
    (AlgebraicCurve.RationalFunctionField.placeInfty K)).nonempty
end AlgebraicCurves.Places.Rational.Proofs.RationalFieldPlaceRatFuncTower
end ProofImplementation
