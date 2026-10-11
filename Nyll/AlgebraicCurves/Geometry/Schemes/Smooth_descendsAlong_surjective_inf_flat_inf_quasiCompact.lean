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

import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Descent

/-!
# Smooth descends Along surjective inf flat inf quasi Compact
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MorphismProperty

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

theorem desc_smooth_descendsAlong :
    DescendsAlong ((fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Smooth h) : MorphismProperty Scheme.{u})
      ((fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) ⊓ (fun {X Y : Scheme.{u}} (h : X ⟶ Y)
        => Flat h) ⊓ (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => QuasiCompact h)) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Smooth h) :=
    smooth_isStableUnderBaseChange
  exact HasRingHomProperty.descendsAlong_flat
    (P := fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Smooth h)
    (Q := RingHom.Smooth) RingHom.Smooth.codescendsAlong_faithfullyFlat

end AlgebraicGeometry

open CategoryTheory _root_.CategoryTheory.MorphismProperty _root_.AlgebraicGeometry
  AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong ((fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Smooth h) : MorphismProperty Scheme.{u})
      ((fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) ⊓ (fun {X Y : Scheme.{u}} (h : X ⟶ Y)
        => Flat h) ⊓ (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => QuasiCompact h)) :=
  AlgebraicGeometry.desc_smooth_descendsAlong
end Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
