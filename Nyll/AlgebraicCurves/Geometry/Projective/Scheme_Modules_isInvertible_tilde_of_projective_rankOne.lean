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

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_tilde

/-!
# Scheme Modules is Invertible tilde of projective rank One
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace Scheme_Modules_isInvertible_tilde_of_projective_rankOne
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem _root_.AlgebraicGeometry.Scheme.Modules.isInvertible_tilde_of_projective_rankOne {R :
  CommRingCat.{u}} (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Projective R P]
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = 1) :
    Scheme.Modules.IsInvertible (tilde P) :=
  (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible (tilde P)).mp
    (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_tilde P 1 hrk)
end Scheme_Modules_isInvertible_tilde_of_projective_rankOne
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
