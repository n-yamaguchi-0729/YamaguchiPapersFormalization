/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Pullback isomorphisms from bijective sections

A map to the pushforward along an open immersion induces an isomorphism after pullback
when its components are bijective over opens contained in the image.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
    AlgebraicGeometry.Scheme.Modules

theorem
  _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : Y.Modules) (L : X.Modules)
    (π : L ⟶ (Scheme.Modules.pushforward f).obj M)
    (hπ : ∀ U : X.Opens, U ≤ f.opensRange → Function.Bijective (π.app U)) :
    Nonempty ((Scheme.Modules.pullback f).obj L ≅ M) := by
  have : IsIso ((restrictFunctor f).map π) := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    exact (ConcreteCategory.isIso_iff_bijective (((restrictFunctor f).map π).app U)).mpr
      (hπ _ (f.image_le_opensRange U))
  exact ⟨((restrictFunctorIsoPullback f).app L).symm ≪≫ asIso ((restrictFunctor f).map π) ≪≫
    (restrictFunctorAdjCounitIso f).app M⟩
end Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
