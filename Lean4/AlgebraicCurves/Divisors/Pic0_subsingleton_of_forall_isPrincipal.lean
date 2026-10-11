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
# Pic0 subsingleton of forall is Principal
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_subsingleton_of_forall_isPrincipal

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

end

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Pic0.subsingleton_of_forall_isPrincipal (K F : Type*) [Field K]
  [Field F] [Algebra K F]
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal) :
    Subsingleton (Pic0 K F) :=
  (QuotientAddGroup.subsingleton_iff.trans AddSubgroup.addSubgroupOf_eq_top).mpr
    fun D hD => Divisor.mem_principal.mpr (h D hD)
end JacobianVarieties.Pic0.Proofs.Pic0_subsingleton_of_forall_isPrincipal
end ProofImplementation
