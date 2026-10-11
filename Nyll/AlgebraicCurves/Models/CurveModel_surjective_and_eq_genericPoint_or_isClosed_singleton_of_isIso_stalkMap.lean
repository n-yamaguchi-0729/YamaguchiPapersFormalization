/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint

/-!
# Curve Model surjective and eq generic Point or is Closed singleton of is Iso stalk Map
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModelPointClassification

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace PointsL8

theorem eq_genericPoint_of_isField {C : Scheme.{u}} [IsIntegral C] (x : C)
    (hfield : IsField (C.presheaf.stalk x)) : x = genericPoint C := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := C) (x := x) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let := C.presheaf.algebra_section_stalk (⟨_, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨_, hxU⟩
  have hbot : (hU.primeIdealOf ⟨_, hxU⟩).asIdeal = ⊥ := by
    rw [← Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective (C.presheaf.stalk x)
      (hU.primeIdealOf ⟨_, hxU⟩).asIdeal.primeCompl_le_nonZeroDivisors),
      IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨_, hxU⟩).asIdeal,
      ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hfield
  have h1 : hU.primeIdealOf ⟨_, hxU⟩ = hU.primeIdealOf ⟨genericPoint C,
      ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
        (by simpa using (inferInstance : Nonempty U))⟩ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    ext1
    exact hbot
  have h2 := congr(hU.fromSpec $h1)
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h2

end PointsL8

end AlgebraicCurves.Models.Proofs.CurveModelPointClassification

section PublicStatement

universe u v
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicCurve
open _root_.AlgebraicCurves.Models.Proofs.CurveModelPointClassification

namespace AlgebraicCurve.CurveModel

theorem surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]
      [IsProper c]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C))) :
    Function.Surjective ν.base ∧ ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C) := by
  classical
  have : IsProper ν := by
    have : IsProper (ν ≫ c) := hν ▸ inferInstance
    exact IsProper.of_comp ν c
  have hclosed : IsClosedMap ν.base := ν.isClosedMap
  have hη : ν.base (genericPoint M.C) = genericPoint C := by
    apply PointsL8.eq_genericPoint_of_isField
    exact MulEquiv.isField (Field.toIsField M.C.functionField)
      (asIso (ν.stalkMap (genericPoint M.C))).commRingCatIsoToRingEquiv.toMulEquiv
  have hsurj : Function.Surjective ν.base := by
    have hr : IsClosed (Set.range ν.base) := hclosed.isClosed_range
    have hdense : closure ({genericPoint C} : Set C) ⊆ Set.range ν.base :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨_, hη⟩) hr
    rw [(genericPoint_spec C).def] at hdense
    intro z
    exact hdense (Set.mem_univ z)
  refine ⟨hsurj, fun z => ?_⟩
  obtain ⟨m, rfl⟩ := hsurj z
  by_cases hm : m = genericPoint M.C
  · exact Or.inl (by rw [hm, hη])
  · right
    have hc := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M.toBase m hm
    have := hclosed _ hc
    rwa [Set.image_singleton] at this

end AlgebraicCurve.CurveModel

end PublicStatement
end ProofImplementation
