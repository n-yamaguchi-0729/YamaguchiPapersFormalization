/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Models.OpenBoundary
import AlgebraicCurves.Models.CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
import Mathlib.AlgebraicGeometry.Restrict

/-! # Interior ramification of an actual open restriction -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicCurves.Models.Proofs
open CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The actual formally unramified open restriction forces ramification
index one at every place of its interior. -/
theorem ramificationIndexAlong_eq_one_outside_openBoundary
    {K F E : Type} [Field K] [IsAlgClosed K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
    (hgen : N.C.fromSpecStalk (genericPoint N.C) ≫ d =
      Spec.map (CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C))
    {Y : Scheme} (k : Y ⟶ N.C) [IsOpenImmersion k]
    [FormallyUnramified (k ≫ d)]
    (w : Place K E) (hw : w ∉ N.openBoundaryPlaces k) :
    Place.ramificationIndexAlong φ w = 1 := by
  let y := N.pointEquivPlace.symm w
  have hy : y.val (IsLocalRing.closedPoint K) =
      (N.placeEquiv.symm w).val := by
    change (pointEquivClosedPoint N.toBase y).val = _
    apply congrArg Subtype.val
    apply N.placeEquiv.injective
    change N.pointEquivPlace y = N.placeEquiv (N.placeEquiv.symm w)
    rw [N.placeEquiv.apply_symm_apply]
    exact N.pointEquivPlace.apply_symm_apply w
  have hyV : y.val (IsLocalRing.closedPoint K) ∈ k.opensRange := by
    rw [hy]
    exact not_not.mp hw
  have hV : FormallyUnramified (k.opensRange.ι ≫ d) := by
    have h : FormallyUnramified (k.isoOpensRange.inv ≫ (k ≫ d)) :=
      MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance
    simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using h
  have h := CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
    N M φ hφ d hd hgen y k.opensRange hyV hV
  simpa only [y, N.pointEquivPlace.apply_symm_apply] using h

end AlgebraicCurve.CurveModel
