/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_placesOf_preimage_subset_preimage_restrictAlong_placesOf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Places
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Places.Exists_place_range_stalk_eq
import Nyll.AlgebraicCurves.Models.Exists_closedPoint_range_stalk_eq
import Nyll.AlgebraicCurves.Models.Eq_of_range_stalk_eq

/-!
# Places Of preimage subset preimage restrict Along places Of
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.PlacesOf_preimage_subset_preimage_restrictAlong_placesOf

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
      exact (congrArg
        (fun f : X.presheaf.stalk (π y) ⟶ Y.functionField =>
          Spec.map f ≫ X.fromSpecStalk (π y)) eX).trans
        ((Spec.map_comp_assoc
          (X.presheaf.stalkSpecializes (genericPoint_specializes (π y)))
          (CommRingCat.ofHom φ) (X.fromSpecStalk (π y))).trans
          ((congrArg
            (fun f : Spec X.functionField ⟶ X => Spec.map (CommRingCat.ofHom φ) ≫ f)
            (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X)
              (genericPoint_specializes (π y)))).trans hφπ.symm))
    have l2 : Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      exact (congrArg
        (fun f : X.presheaf.stalk (π y) ⟶ Y.functionField =>
          Spec.map f ≫ X.fromSpecStalk (π y)) eY).trans
        ((Spec.map_comp_assoc (π.stalkMap y)
          (Y.presheaf.stalkSpecializes (genericPoint_specializes y))
          (X.fromSpecStalk (π y))).trans
          ((congrArg
            (fun f : Spec (Y.presheaf.stalk y) ⟶ X =>
              Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes y)) ≫ f)
            (Scheme.SpecMap_stalkMap_fromSpecStalk (f := π) (x := y))).trans
            (Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc
              (X := Y) (genericPoint_specializes y) π)))
    rw [← cancel_mono (X.fromSpecStalk (π y)), l1, l2]
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

theorem _root_.AlgebraicCurve.placesOf_preimage_subset_preimage_restrictAlong_placesOf
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [SmoothOfRelativeDimension 1 cX]
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
    placesOf cY (π ⁻¹ᵁ U) ⊆ (Place.restrictAlong φ hφ) ⁻¹' placesOf cX U := by
  let := (baseToFunctionField cX).toAlgebra
  let := (baseToFunctionField cY).toAlgebra
  rintro w ⟨y, hyU, hyc, hyw⟩
  have hxc : IsClosed ({π y} : Set X) := by
    rw [← Set.image_singleton]; exact π.isClosedMap _ hyc
  obtain ⟨v, hv⟩ := exists_place_range_stalk_eq cX (π y) hxc
  refine ⟨π y, hyU, hxc, ?_⟩
  rw [hv, AlgebraicCurve.GlueAux.eq_restrictAlong_of_range_stalk_eq cX cY π φ hφ hφπ y w v hyw hv]
end AlgebraicCurves.Places.Proofs.PlacesOf_preimage_subset_preimage_restrictAlong_placesOf
end ProofImplementation
