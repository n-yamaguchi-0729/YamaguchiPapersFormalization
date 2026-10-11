/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SchemeFibreEndo.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Scheme Fibre Endo
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- The endomorphism induced on a scheme fibre by an endomorphism over the base. -/
def schemeFibreEndo {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hcomm : h ≫ f = f)
    (s : S) :
    Limits.pullback f (S.fromSpecResidueField s)
      ⟶ Limits.pullback f (S.fromSpecResidueField s) :=
  Limits.pullback.lift (Limits.pullback.fst _ _ ≫ h) (Limits.pullback.snd _ _)
    (by rw [Category.assoc, hcomm, Limits.pullback.condition])

@[simp] theorem schemeFibreEndo_fst {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X)
    (hcomm : h ≫ f = f) (s : S) :
    schemeFibreEndo f h hcomm s ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ h :=
  Limits.pullback.lift_fst _ _ _

@[simp] theorem schemeFibreEndo_snd {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X)
    (hcomm : h ≫ f = f) (s : S) :
    schemeFibreEndo f h hcomm s ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ :=
  Limits.pullback.lift_snd _ _ _

end AlgebraicGeometry
