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

import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank

/-!
# Local freeness preserved by isomorphisms

Transfers local freeness of a fixed rank along an isomorphism of scheme modules.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsLocallyFreeOfRank_of_iso

universe u
open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_iso {X : Scheme.{u}} {n :
  ℕ} {M N : X.Modules} (e : M ≅ N) (h : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsLocallyFreeOfRank n N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨i⟩⟩ := h.exists_trivialization x
  exact ⟨U, hx, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ i⟩⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsLocallyFreeOfRank_of_iso
end ProofImplementation
