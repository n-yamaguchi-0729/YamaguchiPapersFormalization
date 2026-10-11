/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_preimage_restrictAlong_placesOf_subset_placesOf_preimage.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Places
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Places.Exists_place_range_stalk_eq
import AlgebraicCurves.Models.Exists_closedPoint_range_stalk_eq
import AlgebraicCurves.Models.Eq_of_range_stalk_eq

/-!
# Preimage restrict Along places Of subset places Of preimage
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Preimage_restrictAlong_placesOf_subset_placesOf_preimage

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace GlueAux
open _root_.AlgebraicCurve

theorem comp_algebraMap_stalk_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X))
    (y : Y) :
    φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField) =
      (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom := by
  have eX : CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField)) =
      X.presheaf.stalkSpecializes (genericPoint_specializes (π y)) ≫ CommRingCat.ofHom φ := rfl
  have eY : CommRingCat.ofHom ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap
    y).hom) =
      π.stalkMap y ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes y) := rfl
  have key : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y))
    X.functionField))) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) := by
    have l1 : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y))
      X.functionField))) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      let α : X.presheaf.stalk (π y) ⟶ X.functionField :=
        X.presheaf.stalkSpecializes (genericPoint_specializes (π y))
      let β : X.functionField ⟶ Y.functionField := CommRingCat.ofHom φ
      have hmap : Spec.map (α ≫ β) = Spec.map β ≫ Spec.map α := Spec.map_comp α β
      have hstalk : Spec.map α ≫ X.fromSpecStalk (π y) =
          X.fromSpecStalk (genericPoint X) :=
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes (π y))
      exact (eq_whisker (congrArg
        (fun f : X.presheaf.stalk (π y) ⟶ Y.functionField => Spec.map f) eX)
        (X.fromSpecStalk (π y))).trans
        ((eq_whisker hmap (X.fromSpecStalk (π y))).trans
          ((Category.assoc _ _ _).trans
            ((whisker_eq (Spec.map β) hstalk).trans hφπ.symm)))
    have l2 : Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      let γ : X.presheaf.stalk (π y) ⟶ Y.presheaf.stalk y := π.stalkMap y
      let δ : Y.presheaf.stalk y ⟶ Y.functionField :=
        Y.presheaf.stalkSpecializes (genericPoint_specializes y)
      have hmap : Spec.map (γ ≫ δ) = Spec.map δ ≫ Spec.map γ := Spec.map_comp γ δ
      have hstalk : Spec.map γ ≫ X.fromSpecStalk (π y) = Y.fromSpecStalk y ≫ π :=
        Scheme.SpecMap_stalkMap_fromSpecStalk π
      have hgen : Spec.map δ ≫ Y.fromSpecStalk y = Y.fromSpecStalk (genericPoint Y) :=
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
      exact (eq_whisker (congrArg
        (fun f : X.presheaf.stalk (π y) ⟶ Y.functionField => Spec.map f) eY)
        (X.fromSpecStalk (π y))).trans
        ((eq_whisker hmap (X.fromSpecStalk (π y))).trans
          ((Category.assoc _ _ _).trans
            ((whisker_eq (Spec.map δ) hstalk).trans
              ((Category.assoc _ _ _).symm.trans (eq_whisker hgen π)))))
    exact (cancel_mono (X.fromSpecStalk (π y))).mp (l1.trans l2.symm)
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

theorem place_eq_of_le {K F : Type*} [Field K] [Field F] [Algebra K F] {v w : Place K F}
    (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w :=
  Place.ext (ValuationSubring.eq_of_le_of_ne_top _ h w.ne_top')

theorem eq_restrictAlong_of_range_stalk_eq
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      X.functionField →ₐ[K] Y.functionField)
    (hφ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      φ.toRingHom.IsIntegral)
    (hφπ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
    (y : Y) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    ∀ (w : Place K Y.functionField) (v : Place K X.functionField),
      (algebraMap (Y.presheaf.stalk y) Y.functionField).range = w.toValuationSubring.toSubring →
      (algebraMap (X.presheaf.stalk (π y)) X.functionField).range = v.toValuationSubring.toSubring →
      v = Place.restrictAlong φ hφ w := by
  let := (baseToFunctionField cX).toAlgebra
  let := (baseToFunctionField cY).toAlgebra
  intro w v hyw hv
  have hc := comp_algebraMap_stalk_eq π φ.toRingHom hφπ y
  apply place_eq_of_le
  intro f hf
  have hf' : f ∈ (algebraMap (X.presheaf.stalk (π y)) X.functionField).range := by
    rw [hv]; exact hf
  obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hf'
  change φ.toRingHom (algebraMap _ _ g) ∈ w.toValuationSubring
  rw [← RingHom.comp_apply, hc, RingHom.comp_apply, ← ValuationSubring.mem_toSubring, ← hyw]
  exact RingHom.mem_range_self _ _

end AlgebraicCurve.GlueAux

theorem _root_.AlgebraicCurve.preimage_restrictAlong_placesOf_subset_placesOf_preimage
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [IsSeparated cX] [SmoothOfRelativeDimension 1 cX]
    [IsProper cY] [SmoothOfRelativeDimension 1 cY]
    (π : Y ⟶ X) [UniversallyClosed π]
    (φ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      X.functionField →ₐ[K] Y.functionField)
    (hφ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      φ.toRingHom.IsIntegral)
    (hφπ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    (Place.restrictAlong φ hφ) ⁻¹' placesOf cX U ⊆ placesOf cY (π ⁻¹ᵁ U) := by
  let := (baseToFunctionField cX).toAlgebra
  let := (baseToFunctionField cY).toAlgebra
  rintro w ⟨x, hxU, hxc, hxw⟩
  obtain ⟨y, hyc, hyw⟩ := exists_closedPoint_range_stalk_eq cY w
  have hπyc : IsClosed ({π y} : Set X) := by
    rw [← Set.image_singleton]; exact π.isClosedMap _ hyc
  obtain ⟨v, hv⟩ := exists_place_range_stalk_eq cX (π y) hπyc
  have hveq := AlgebraicCurve.GlueAux.eq_restrictAlong_of_range_stalk_eq cX cY π φ hφ hφπ y w v
    hyw hv
  have hπy : π y = x := eq_of_range_stalk_eq cX (π y) x (by rw [hv, hxw, hveq])
  refine ⟨y, ?_, hyc, hyw⟩
  change π y ∈ U
  rw [hπy]; exact hxU
end AlgebraicCurves.Places.Proofs.Preimage_restrictAlong_placesOf_subset_placesOf_preimage
end ProofImplementation
