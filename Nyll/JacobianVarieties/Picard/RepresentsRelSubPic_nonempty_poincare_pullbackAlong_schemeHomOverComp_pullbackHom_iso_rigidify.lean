/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_rigidify_iso_of_nonempty_pullback_iso_unit

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
/-!
# Poincare bundles under pullback of curves

Pullback on the representing Picard scheme agrees with rigidification of the pulled-back
Poincare bundle on the changed curve.
-/

section ProofImplementation

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


universe u

theorem nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong
        (NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom f hf hε h h'))).L ≅
      Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L)) := by
  have hM : (algEquivZeroCut c ε).P t (h.poincare.pullbackAlong a) :=
    (algEquivZeroCut c ε).pullback_mem _ _ a _ h.poincare_mem
  have ha : a = h.classify t _ hM := h.classify_unique t _ hM a ⟨Iso.refl _⟩
  have key := RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε h h' t _ hM
  have hspec := h'.classify_spec t ((h.poincare.pullbackAlong a).pullbackCurve f hf hε)
    (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM)
  rw [← key, ← ha] at hspec
  obtain ⟨e₁⟩ := hspec
  obtain ⟨e₂⟩ :=
    AlgebraicGeometry.Scheme.Modules.nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
    (rigSection c' t ε') (pullback.snd c' t) _
    ((h.poincare.pullbackAlong a).pullbackCurve f hf hε).rigidified
  exact ⟨e₁ ≪≫ e₂.symm⟩
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation
