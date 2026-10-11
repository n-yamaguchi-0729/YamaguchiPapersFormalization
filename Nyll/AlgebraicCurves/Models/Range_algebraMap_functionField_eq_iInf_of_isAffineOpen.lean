/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Geometry.Schemes.IsAffineOpen_range_algebraMap_functionField_eq_iInf
import Nyll.AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import Nyll.AlgebraicCurves.Places.Exists_place_range_stalk_eq

/-!
# Range algebraMap functionField eq iInf of isAffineOpen

The image of the coordinate ring of an affine curve open is the intersection of its local
valuation subrings in the function field.
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.Range_algebraMap_functionField_eq_iInf_of_isAffineOpen

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem _root_.AlgebraicCurve.range_algebraMap_functionField_eq_iInf_of_isAffineOpen
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (algebraMap Γ(C, U) C.functionField).range =
      ⨅ (v : AlgebraicCurve.Place K C.functionField)
        (_ : ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
          (algebraMap (C.presheaf.stalk x) C.functionField).range =
            v.toValuationSubring.toSubring),
        v.toValuationSubring.toSubring := by
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  rw [hU.range_algebraMap_functionField_eq_iInf]
  apply le_antisymm
  · refine le_iInf₂ fun v hv => ?_
    obtain ⟨x, hxU, -, hrange⟩ := hv
    rw [← hrange]
    exact iInf₂_le x hxU
  · refine le_iInf₂ fun x hxU => ?_
    by_cases hη : x = genericPoint C
    · subst hη
      intro f _
      refine ⟨f, ?_⟩
      change (C.presheaf.stalkSpecializes (specializes_refl _)).hom f = f
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    · have hxcl : IsClosed ({x} : Set C) := isClosed_singleton_of_ne_genericPoint c x hη
      obtain ⟨v, hv⟩ := exists_place_range_stalk_eq c x hxcl
      rw [hv]
      exact iInf₂_le v ⟨x, hxU, hxcl, hv⟩
end AlgebraicCurves.Models.Proofs.Range_algebraMap_functionField_eq_iInf_of_isAffineOpen
end ProofImplementation
