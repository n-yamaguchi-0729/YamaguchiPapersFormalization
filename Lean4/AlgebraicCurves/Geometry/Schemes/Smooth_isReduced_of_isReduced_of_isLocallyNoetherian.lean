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

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.MorphismProperty.Limits
import AlgebraicCurves.Geometry.Schemes.isReduced_of_smooth_of_field

/-!
# Smooth is Reduced of is Reduced of is Locally Noetherian
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

universe u

open CategoryTheory AlgebraicGeometry

namespace REDsol

theorem geometricallyReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
  GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact AlgebraicGeometry.isReduced_of_smooth_of_field snd

end REDsol

theorem _root_.AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X := by
  have := REDsol.geometricallyReduced_of_smooth f
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
end AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
end ProofImplementation
