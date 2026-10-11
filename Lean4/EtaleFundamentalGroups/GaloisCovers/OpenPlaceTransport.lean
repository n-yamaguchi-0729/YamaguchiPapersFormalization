/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Models.OpenBoundary
import AlgebraicCurves.Models.FunctionFieldScalarFunctoriality
import AlgebraicCurves.Places.Place_exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
import EtaleFundamentalGroups.GaloisCovers.OpenFunctionField

/-! # Actual interior places under the open function-field identification -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- The literal function-field identification of the open curve preserves
the scalar map from its actual structure morphism. -/
theorem openFunctionFieldEquiv_algebraMap
    (M : CurveModel K F) {X : Scheme} [IsIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (a : K) :
    (M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion)
        (algebraMap K F a) = baseToFunctionField (j ≫ M.toBase) a := by
  change j.functionFieldRingEquivOfIsOpenImmersion
    (M.ffEquiv (algebraMap K F a)) = _
  rw [M.ffEquiv_algebraMap]
  exact Scheme.Hom.functionFieldMap_baseToFunctionField M.toBase j
    (j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j) a

/-- Membership in the valuation ring at an interior model point is
equivalent to membership in the actual local-ring image of the open curve. -/
theorem openFunctionFieldEquiv_mem_stalk_range_iff
    (M : CurveModel K F) {X : Scheme} [IsIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (x : X) (z : closedPoints M.C) (hz : z.val = j x) (a : F) :
    (M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion) a ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range ↔
      a ∈ (M.placeOfPoint z).toValuationSubring := by
  let hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  change j.functionFieldMap hj (M.ffEquiv a) ∈ _ ↔ _
  rw [j.functionFieldMap_mem_stalk_range_iff_of_isOpenImmersion]
  rw [← hz]
  have hmodel : M.ffEquiv a ∈
      (algebraMap (M.C.presheaf.stalk z.val) M.C.functionField).range ↔
      a ∈ ((M.ffEquiv.symm.toRingHom).comp
        (algebraMap (M.C.presheaf.stalk z.val) M.C.functionField)).range := by
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      change M.ffEquiv.symm (algebraMap _ _ b) = a
      rw [hb, M.ffEquiv.symm_apply_apply]
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      have hb' : M.ffEquiv.symm (algebraMap _ _ b) = a := hb
      apply M.ffEquiv.symm.injective
      exact hb'.trans (M.ffEquiv.symm_apply_apply a).symm
  rw [hmodel, M.range_stalk_eq z]
  rfl

/-- Every interior place has its transported valuation ring equal to the
actual stalk image, and its order function is unchanged. The equivalence
of places is obtained from the existing field-isomorphism theorem. -/
theorem exists_openPlaceEquiv_stalk_range_ord
    (M : CurveModel K F) {X : Scheme} [IsIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j] :
    let : Algebra K X.functionField := (baseToFunctionField (j ≫ M.toBase)).toAlgebra
    ∃ Φ : Place K F ≃ Place K X.functionField,
      (∀ (v : Place K F) (a : F),
        (Φ v).ord ((M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion) a) =
          v.ord a) ∧
      ∀ v : Place K F, v ∉ M.openBoundaryPlaces j →
        ∃ x : closedPoints X,
          (algebraMap (X.presheaf.stalk x.val) X.functionField).range =
            (Φ v).toValuationSubring.toSubring := by
  intro algX
  let e := M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion
  obtain ⟨Φ, hΦ, hord, _⟩ :=
    Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
      (RingEquiv.refl K) e (fun a => M.openFunctionFieldEquiv_algebraMap j a)
  refine ⟨Φ, hord, ?_⟩
  intro v hv
  obtain ⟨x, hx⟩ := M.exists_closedPoint_of_not_mem_openBoundaryPlaces j v hv
  refine ⟨x, ?_⟩
  ext b
  have hmem := M.openFunctionFieldEquiv_mem_stalk_range_iff j x.val
    (M.placeEquiv.symm v) hx.symm (e.symm b)
  change e (e.symm b) ∈ _ ↔ _ at hmem
  rw [e.apply_symm_apply] at hmem
  have hp : M.placeOfPoint (M.placeEquiv.symm v) = v :=
    M.placeEquiv.apply_symm_apply v
  rw [hp] at hmem
  change b ∈ (algebraMap (X.presheaf.stalk x.val) X.functionField).range ↔
    b ∈ (Φ v).toValuationSubring
  rw [hΦ v]
  exact hmem

end AlgebraicCurve.CurveModel
