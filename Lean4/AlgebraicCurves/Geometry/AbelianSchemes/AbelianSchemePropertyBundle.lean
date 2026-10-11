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

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import AlgebraicCurves.Geometry.Picard.RelativeGroupLaw

/-!
Smoothness, properness, connected fibres and existence of a relative group law over an affine
base.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian

section AbstractCarriers

variable (R : Type u) [CommRing R]

/-- The smooth, proper, connected-fibre and group-law properties of a morphism over Spec R. -/
structure AbelianSchemePropertyBundle {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) :
    Prop where
  /-- The structure morphism is smooth. -/
  smooth : Smooth f
  /-- The structure morphism is proper. -/
  proper : IsProper f
  /-- Every fibre of the structure morphism is connected. -/
  connectedFibres : ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s})
  /-- The structure morphism admits a relative group law. -/
  hasGroupLaw : Nonempty (RelativeGroupLaw R f)

end AbstractCarriers

end GoodReductionJacobian
