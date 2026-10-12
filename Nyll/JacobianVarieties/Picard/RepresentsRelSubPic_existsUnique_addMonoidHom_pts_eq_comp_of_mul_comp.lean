/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_eq_comp_of_mul_comp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange
import Mathlib.Util.WithWeakNamespace

/-!
# The additive map induced by a multiplicative scheme map
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.AdditivePointMap


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.SmoothProperCurve


universe u

with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic
theorem existsUnique_addMonoidHom_pts_eq_comp_of_mul_comp
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (J : Type u) [AddCommGroup J]
    (pts : J ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase)
    (hadd : ∀ a b : J, Nonempty
      ((h.poincare.pullbackAlong (pts (a + b))).L ≅
        (h.poincare.pullbackAlong (pts a)).L ⊗ (h.poincare.pullbackAlong (pts b)).L))
    (ψ : SchemeHomOver D.toBase D.toBase)
    (hψmul : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) ψ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
          (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)) :
    ∃! e : J →+ J, ∀ y : J, (pts (e y)).1 = (pts y).1 ≫ ψ.1 := by
  classical
  have hQadd : ∀ a b : J, pts (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _
        (pts a) (pts b) := by
    intro a b
    apply h.ext_of_iso
    obtain ⟨eab⟩ := hadd a b
    obtain ⟨emul⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso
      (P := algEquivZeroGroupCut c ε) h (T := Over.mk (𝟙 (Spec (CommRingCat.of R))))
      (schemeHomOverToOverHom (pts a)) (schemeHomOverToOverHom (pts b))
    exact ⟨eab ≪≫ emul.symm⟩
  let e₀ : J → J := fun y => pts.symm (NeronModelInfra.schemeHomOverComp (pts y) ψ)
  have hread : ∀ y : J, pts (e₀ y) = NeronModelInfra.schemeHomOverComp (pts y) ψ :=
    fun y => Equiv.apply_symm_apply _ _
  have hadd' : ∀ a b : J, e₀ (a + b) = e₀ a + e₀ b := by
    intro a b
    apply pts.injective
    rw [hread, hQadd, hψmul, hQadd, hread, hread]
  refine ⟨AddMonoidHom.mk' e₀ hadd', fun y => congrArg Subtype.val (hread y), ?_⟩
  intro e' he'
  ext y
  apply pts.injective
  rw [show pts ((AddMonoidHom.mk' e₀ hadd') y) = pts (e₀ y) from rfl, hread]
  exact Subtype.ext (he' y)
end JacobianVarieties.Picard.Proofs.AdditivePointMap
end ProofImplementation
