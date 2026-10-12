/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardThetaBundle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.AlgebraicCurves.Geometry.Sheaves.RelativeSectionTwist

/-!
# Relative Picard and theta bundles

The Picard bundle pushes a tensor product of a rigidified line bundle and a module
forward to the test scheme. The theta bundle is the dual of the determinant of this
pushforward after twisting by the chosen relative section.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}}
  (t : T ⟶ Spec (CommRingCat.of R))

/-- Push the tensor product with `M` forward along the projection to the test scheme. -/
def picardBundle (M : RigidifiedLineBundle c ε t) (N : (pullback c t).Modules) : T.Modules :=
  (Scheme.Modules.pushforward (pullback.snd c t)).obj (M.L ⊗ N)

/-- The dual determinant of the Picard bundle after a relative section twist. -/
def thetaBundle (M : RigidifiedLineBundle c ε t) (r n : ℕ) : T.Modules :=
  Scheme.Modules.dual (Scheme.Modules.det n (picardBundle c ε t M (sectionTwist c ε t r)))

@[simp] theorem picardBundle_def (M : RigidifiedLineBundle c ε t) (N : (pullback c t).Modules) :
    picardBundle c ε t M N = (Scheme.Modules.pushforward (pullback.snd c t)).obj (M.L ⊗ N) := rfl

@[simp] theorem thetaBundle_def (M : RigidifiedLineBundle c ε t) (r n : ℕ) :
    thetaBundle c ε t M r n =
      Scheme.Modules.dual (Scheme.Modules.det n
        (picardBundle c ε t M (sectionTwist c ε t r))) := rfl

end AlgebraicGeometry.RelPicard

end
