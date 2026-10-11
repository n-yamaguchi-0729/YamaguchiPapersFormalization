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

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Place exists ord eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_ord_eq_one

theorem _root_.AlgebraicCurve.Place.exists_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K
  F] (v : AlgebraicCurve.Place K F) :
    ∃ t : F, v.ord t = 1 :=
  let ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  ⟨π, v.ord_coe_irreducible hπ⟩
end AlgebraicCurves.Places.Proofs.Place_exists_ord_eq_one
end ProofImplementation
