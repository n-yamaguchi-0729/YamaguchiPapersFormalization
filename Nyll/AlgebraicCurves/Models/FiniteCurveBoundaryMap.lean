/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.OpenInteriorRamification
import Nyll.AlgebraicCurves.Models.CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite

/-! # The actual finite curve map and its boundary places -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.AlgebraicCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F E : Type} [Field K] [IsAlgClosed K]
  [Field F] [Field E] [Algebra K F] [Algebra K E]
  (M : CurveModel K F) (N : CurveModel K E)
  (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
  [IsFinite d] (hsurj : Function.Surjective d)

/-- The field map of the original finite morphism, retaining its generic
stalk construction. -/
def finiteCurveFieldMap : F →ₐ[K] E :=
  FFLeg.phi K M N d hd hsurj

omit [IsAlgClosed K] in
/-- The actual finite curve map induces an integral extension of function fields. -/
theorem finiteCurveFieldMap_integral :
    (M.finiteCurveFieldMap N d hd hsurj).toRingHom.IsIntegral :=
  FFLeg.isIntegral_phi K M N d hd hsurj

omit [IsAlgClosed K] in
/-- The actual induced function-field extension is finite. -/
theorem finiteCurveFieldMap_finite :
    FiniteAlong K (M.finiteCurveFieldMap N d hd hsurj) :=
  FFLeg.finiteAlong_phi K M N d hd hsurj

omit [IsAlgClosed K] [IsFinite d] in
/-- The induced function-field map agrees with the original generic-point morphism. -/
theorem finiteCurveFieldMap_generic :
    N.C.fromSpecStalk (genericPoint N.C) ≫ d =
      Spec.map (CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        ((M.finiteCurveFieldMap N d hd hsurj).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
  let φ := M.finiteCurveFieldMap N d hd hsurj
  let ξ := FFLeg.specializes_genericPoint K M N d hsurj
  let g : M.C.functionField →+* N.C.functionField :=
    (FFLeg.FunctionFieldPull.pull d ξ).hom
  have hg : Spec.map (CommRingCat.ofHom g) ≫ M.C.fromSpecStalk (genericPoint M.C) =
      N.C.fromSpecStalk (genericPoint N.C) ≫ d := by
    change Spec.map (M.C.presheaf.stalkSpecializes ξ ≫ d.stalkMap (genericPoint N.C)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have heq : N.ffEquiv.toRingHom.comp
      (φ.toRingHom.comp M.ffEquiv.symm.toRingHom) = g := by
    ext a
    change N.ffEquiv (N.ffEquiv.symm (g (M.ffEquiv (M.ffEquiv.symm a)))) = g a
    rw [N.ffEquiv.apply_symm_apply, M.ffEquiv.apply_symm_apply]
  rw [heq]
  exact hg.symm

omit [IsFinite d] in
private theorem pointEquivPlace_symm_closedPoint
    (P : CurveModel K E) (w : Place K E) :
    (P.pointEquivPlace.symm w).val (IsLocalRing.closedPoint K) =
      (P.placeEquiv.symm w).val := by
  change (pointEquivClosedPoint P.toBase (P.pointEquivPlace.symm w)).val = _
  apply congrArg Subtype.val
  apply P.placeEquiv.injective
  change P.pointEquivPlace (P.pointEquivPlace.symm w) =
    P.placeEquiv (P.placeEquiv.symm w)
  rw [P.pointEquivPlace.apply_symm_apply, P.placeEquiv.apply_symm_apply]

/-- Geometric equality of boundaries becomes the literal preimage of
places under the actual extension map. -/
theorem openBoundaryPlaces_eq_restrict_preimage
    {X Y : Scheme} (j : X ⟶ M.C) (k : Y ⟶ N.C)
    (hboundary : ∀ y : N.C, y ∉ Set.range k ↔ d y ∉ Set.range j) :
    N.openBoundaryPlaces k =
      (fun w : Place K E => w.restrictAlong
        (M.finiteCurveFieldMap N d hd hsurj)
        (M.finiteCurveFieldMap_integral N d hd hsurj)) ⁻¹'
          M.openBoundaryPlaces j := by
  ext w
  let φ := M.finiteCurveFieldMap N d hd hsurj
  let hφ := M.finiteCurveFieldMap_integral N d hd hsurj
  have hpoint := FFLeg.point_compat K M N d hd hsurj w
  have heval := congrArg (fun q => q (IsLocalRing.closedPoint K)) hpoint
  have hM : (M.pointEquivPlace.symm (w.restrictAlong φ hφ)).val
      (IsLocalRing.closedPoint K) = (M.placeEquiv.symm (w.restrictAlong φ hφ)).val := by
    exact pointEquivPlace_symm_closedPoint M _
  have hN := pointEquivPlace_symm_closedPoint N w
  change (M.pointEquivPlace.symm (w.restrictAlong φ hφ)).val
      (IsLocalRing.closedPoint K) =
    d ((N.pointEquivPlace.symm w).val (IsLocalRing.closedPoint K)) at heval
  rw [hM, hN] at heval
  change (N.placeEquiv.symm w).val ∉ Set.range k ↔
    (M.placeEquiv.symm (w.restrictAlong φ hφ)).val ∉ Set.range j
  rw [heval]
  exact hboundary _

/-- Interior ramification is obtained from the actual unramified open
restriction of this same finite morphism. -/
theorem finiteCurveFieldMap_unramified_on_open
    {Y : Scheme} (k : Y ⟶ N.C) [IsOpenImmersion k]
    [FormallyUnramified (k ≫ d)]
    (w : Place K E) (hw : w ∉ N.openBoundaryPlaces k) :
    Place.ramificationIndexAlong (M.finiteCurveFieldMap N d hd hsurj) w = 1 :=
  M.ramificationIndexAlong_eq_one_outside_openBoundary N
    (M.finiteCurveFieldMap N d hd hsurj)
    (M.finiteCurveFieldMap_integral N d hd hsurj) d hd
    (M.finiteCurveFieldMap_generic N d hd hsurj) k w hw

end AlgebraicCurve.CurveModel
