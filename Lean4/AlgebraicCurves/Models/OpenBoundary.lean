/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Models.Finite_compl_of_isOpen
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # The actual finite boundary of an open subscheme of a proper curve -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isProper CurveModel.isIntegral CurveModel.smooth

universe u v

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

/-- The omitted places are exactly those whose actual closed points are
outside the image of the given open immersion. -/
def openBoundaryPlaces (M : CurveModel K F)
    {X : Scheme.{u}} (j : X ⟶ M.C) : Set (Place K F) :=
  {v | (M.placeEquiv.symm v).val ∉ Set.range j}

/-- Interior points avoid the actual boundary set. -/
theorem place_not_mem_openBoundaryPlaces
    (M : CurveModel K F) {X : Scheme.{u}} (j : X ⟶ M.C)
    (y : X) (x : closedPoints M.C) (hx : x.val = j y) :
    M.placeOfPoint x ∉ M.openBoundaryPlaces j := by
  change ¬ (M.placeEquiv.symm (M.placeOfPoint x)).val ∉ Set.range j
  rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
  exact fun h => h ⟨y, hx.symm⟩

/-- The geometric boundary is finite for a nonempty open curve. -/
theorem openBoundaryPlaces_finite
    (M : CurveModel K F) {X : Scheme.{u}} [Nonempty X]
    (j : X ⟶ M.C) [IsOpenImmersion j] :
    (M.openBoundaryPlaces j).Finite := by
  let V : M.C.Opens := ⟨Set.range j, j.isOpenEmbedding.isOpen_range⟩
  have hV : (V : Set M.C).Nonempty :=
    ⟨j (Classical.choice (inferInstance : Nonempty X)), Set.mem_range_self _⟩
  have hf := AlgebraicCurve.finite_compl_of_isOpen M.toBase V hV
  have hi : Function.Injective (fun v : Place K F => (M.placeEquiv.symm v).val) :=
    fun v w h => M.placeEquiv.symm.injective (Subtype.ext h)
  exact Set.Finite.preimage hi.injOn hf

/-- Every place outside the actual boundary is represented by a closed
point of the actual open curve. -/
theorem exists_closedPoint_of_not_mem_openBoundaryPlaces
    (M : CurveModel K F) {X : Scheme.{u}}
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (v : Place K F) (hv : v ∉ M.openBoundaryPlaces j) :
    ∃ x : closedPoints X, j x.val = (M.placeEquiv.symm v).val := by
  classical
  have hmem : (M.placeEquiv.symm v).val ∈ Set.range j := not_not.mp hv
  obtain ⟨x, hx⟩ := hmem
  have hpre : j ⁻¹' ({(M.placeEquiv.symm v).val} : Set M.C) = {x} := by
    ext z
    change j z = (M.placeEquiv.symm v).val ↔ z = x
    rw [← hx]
    exact j.isOpenEmbedding.injective.eq_iff
  have hclosed : IsClosed ({x} : Set X) := by
    rw [← hpre]
    exact (M.placeEquiv.symm v).property.preimage j.continuous
  exact ⟨⟨x, hclosed⟩, hx⟩

end AlgebraicCurve.CurveModel
