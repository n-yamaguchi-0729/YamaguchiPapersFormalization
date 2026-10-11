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

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import SchemeTheory.Modules.TensorSections
import SchemeTheory.Modules.PresheafInternalHom
import SchemeTheory.Modules.SheafificationMonoidal
import AlgebraicCurves.Foundations.Algebra.SheafOfModules_MonoidalV2
import SchemeTheory.Modules.TensorPowers
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionsTensorV2

/-!
# Scheme Modules tensor Pow Section smul monoidal V2
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_tensorPowSection_smul_monoidalV2

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


open AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul_monoidalV2 {X :
  AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U : X.Opens} (g : Γ(X, U)) (s : Γ(L, U)) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPowSection (g • s) n =
      g ^ n • AlgebraicGeometry.Scheme.Modules.tensorPowSection s n := by
  induction n with
  | zero =>
    rw [tensorPowSection_zero, tensorPowSection_zero, pow_zero]
    exact (one_smul Γ(X, U) (unitSection U)).symm
  | succ n ih =>
    rw [tensorPowSection_succ, tensorPowSection_succ, ih, tensorSections_smul_left,
      tensorSections_smul_right,
      smul_smul, ← pow_succ]
    try rfl
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_tensorPowSection_smul_monoidalV2
end ProofImplementation
