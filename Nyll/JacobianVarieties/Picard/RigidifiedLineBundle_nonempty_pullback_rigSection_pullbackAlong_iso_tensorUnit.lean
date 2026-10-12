/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field

/-!
Triviality along a rigidifying section after pulling back a rigidified line bundle from a field.
-/

section ProofImplementation

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

theorem nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
    {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))))
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    Nonempty ((Scheme.Modules.pullback (rigSection c t P)).obj (N.pullbackAlong ⟨t,
      Category.comp_id t⟩).L ≅
      𝟙_ T.Modules) := by
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
    ((Scheme.Modules.pullback (rigSection c (𝟙 _) P)).obj N.L) (N.isInvertible.pullback _)
  exact ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c P ⟨t, Category.comp_id t⟩)).app N.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N.L).symm ≪≫
    (Scheme.Modules.pullback t).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso t⟩
end AlgebraicGeometry.RelPicard.RigidifiedLineBundle
end ProofImplementation
