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
# Place adicValuation isRankOneDiscrete

The adic valuation attached to a place is discrete of rank one.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_adicValuation_isRankOneDiscrete

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Places.Proofs.Place_adicValuation_isRankOneDiscrete.AlgebraicCurve in
theorem _root_.AlgebraicCurve.Place.adicValuation_isRankOneDiscrete {K F : Type*} [Field K]
  [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete :=
  AlgebraicCurve.Place.rowMain v
end AlgebraicCurves.Places.Proofs.Place_adicValuation_isRankOneDiscrete
end ProofImplementation
