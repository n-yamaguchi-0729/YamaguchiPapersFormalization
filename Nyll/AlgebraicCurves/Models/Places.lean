/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_PlacesOf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Models.Basic

/-!
# Places

Open subsets of a curve determine sets of places through their closed-point local rings.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]

/-- The places given by closed-point local rings at points of the specified curve open. -/
def placesOf (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    Set (Place K C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  {v | ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
    (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring}

theorem mem_placesOf_iff (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, v ∈ placesOf c U ↔ ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring :=
  fun _ => Iff.rfl

theorem placesOf_mono {U V : C.Opens} (h : U ≤ V) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c U ⊆ placesOf c V := by
  rintro v ⟨x, hxU, hx, hv⟩
  exact ⟨x, h hxU, hx, hv⟩

theorem placesOf_sup (U V : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (U ⊔ V) = placesOf c U ∪ placesOf c V := by
  let := (baseToFunctionField c).toAlgebra
  apply Set.Subset.antisymm
  · rintro v ⟨x, hxUV, hx, hv⟩
    rcases (show x ∈ (U : Set C) ∪ (V : Set C) from hxUV) with h | h
    · exact Or.inl ⟨x, h, hx, hv⟩
    · exact Or.inr ⟨x, h, hx, hv⟩
  · rintro v (h | h)
    · exact placesOf_mono c le_sup_left h
    · exact placesOf_mono c le_sup_right h

theorem placesOf_bot :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (⊥ : C.Opens) = ∅ := by
  let := (baseToFunctionField c).toAlgebra
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, hx, -, -⟩
  exact hx

end AlgebraicCurve

end
