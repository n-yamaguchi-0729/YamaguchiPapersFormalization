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

import Nyll.JacobianVarieties.WeilPairing.Datum

/-!
Interchanging the two divisors in Weil pairing data inverts the pairing.
-/

section ProofImplementation

namespace JacobianVarieties.WeilPairing.Proofs.WeilDatum_symm_pairing

open AlgebraicCurve

theorem _root_.AlgebraicCurve.WeilDatum.symm_pairing {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} (d : WeilDatum K F n) : d.symm.pairing = d.pairing⁻¹ := by
  rw [WeilDatum.pairing, WeilDatum.pairing, inv_div]
  rfl
end JacobianVarieties.WeilPairing.Proofs.WeilDatum_symm_pairing
end ProofImplementation
