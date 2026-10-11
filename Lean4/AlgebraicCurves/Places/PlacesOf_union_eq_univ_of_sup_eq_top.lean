/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Models.Places
import AlgebraicCurves.Models.Exists_closedPoint_range_stalk_eq
import AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import AlgebraicCurves.Places.Exists_place_range_stalk_eq
import AlgebraicCurves.Models.Eq_of_range_stalk_eq

/-!
# PlacesOf union eq univ of sup eq top

A cover of a curve by two open subsets gives a cover of all its places by their associated place
sets.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.PlacesOf_union_eq_univ_of_sup_eq_top

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]

theorem placesOf_top [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (⊤ : C.Opens) = Set.univ := by
  let := (baseToFunctionField c).toAlgebra
  refine Set.eq_univ_of_forall fun v => ?_
  obtain ⟨x, hx, hv⟩ := exists_closedPoint_range_stalk_eq c v
  exact ⟨x, trivial, hx, hv⟩

theorem exists_not_mem_placesOf [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (baseToFunctionField c).toAlgebra
    ∃ v : Place K C.functionField, v ∉ placesOf c U := by
  let := (baseToFunctionField c).toAlgebra
  have hUne : (U : Set C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hU0 : U = ⊥ := Opens.ext h
    rw [hU0, bot_sup_eq] at hUV
    exact hV hUV
  have hη : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hUne)
  obtain ⟨x, hxU⟩ : ∃ x : C, x ∉ U :=
    not_forall.mp fun h => hU (Opens.ext (Set.eq_univ_of_forall h))
  have hxη : x ≠ genericPoint C := fun h => hxU (h ▸ hη)
  have hxcl := isClosed_singleton_of_ne_genericPoint c x hxη
  obtain ⟨v, hv⟩ := exists_place_range_stalk_eq c x hxcl
  refine ⟨v, ?_⟩
  rintro ⟨y, hyU, -, hvy⟩
  have hxy : x = y := eq_of_range_stalk_eq c x y (hv.trans hvy.symm)
  exact hxU (hxy ▸ hyU)

theorem placesOf_union_eq_univ_of_sup_eq_top' [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c U ∪ placesOf c V = Set.univ ∧
      (∃ v : Place K C.functionField, v ∉ placesOf c U) ∧
      (∃ v : Place K C.functionField, v ∉ placesOf c V) := by
  let := (baseToFunctionField c).toAlgebra
  refine ⟨?_, exists_not_mem_placesOf c U V hUV hU hV,
    exists_not_mem_placesOf c V U (sup_comm U V ▸ hUV) hV hU⟩
  rw [← placesOf_sup, hUV, placesOf_top]

end AlgebraicCurve

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Places.Proofs.PlacesOf_union_eq_univ_of_sup_eq_top.AlgebraicCurve in
theorem _root_.AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top {K : Type u} [Field K] {C :
  Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    AlgebraicCurve.placesOf c U ∪ AlgebraicCurve.placesOf c V = Set.univ ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c U) ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c V) :=
  placesOf_union_eq_univ_of_sup_eq_top' c U V hUV hU hV
end AlgebraicCurves.Places.Proofs.PlacesOf_union_eq_univ_of_sup_eq_top
end ProofImplementation
