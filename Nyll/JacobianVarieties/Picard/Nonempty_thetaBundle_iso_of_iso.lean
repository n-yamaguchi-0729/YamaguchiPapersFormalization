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

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.JacobianVarieties.Picard.ThetaBundle

/-!
Transport theta bundles along an isomorphism of the underlying rigidified line bundles.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.Nonempty_thetaBundle_iso_of_iso

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

theorem _root_.AlgebraicGeometry.RelPicard.nonempty_thetaBundle_iso_of_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec
      (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (e : M.L ≅ M'.L) (r n : ℕ) :
    Nonempty (thetaBundle c ε t M r n ≅ thetaBundle c ε t M' r n) := by
  let i1 : M.L ⊗ sectionTwist c ε t r ≅ M'.L ⊗ sectionTwist c ε t r := whiskerRightIso e _
  let i2 := (Scheme.Modules.pushforward (pullback.snd c t)).mapIso i1
  let i3 := (Scheme.Modules.exteriorPower T n).mapIso i2
  exact ⟨(MonoidalClosed.internalHom.mapIso i3.symm.op).app (𝟙_ T.Modules)⟩
end JacobianVarieties.Picard.Proofs.Nonempty_thetaBundle_iso_of_iso
end ProofImplementation
