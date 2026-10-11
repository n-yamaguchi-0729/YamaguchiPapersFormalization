/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Sections on an affine open inside the function field

The image of the section ring of a nonempty affine open in the function field is the
intersection of the images of the stalks at points of that open.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace IsAffineOpen_range_algebraMap_functionField_eq_iInf

open CategoryTheory AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.IsAffineOpen.range_algebraMap_functionField_eq_iInf
    {X : Scheme.{u}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    (algebraMap Γ(X, U) X.functionField).range =
      ⨅ (x : X) (_ : x ∈ U), (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  set A := Γ(X, U) with hA
  set F := X.functionField with hF
  have hfrac : IsFractionRing A F := functionField_isFractionRing_of_isAffineOpen X U hU
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    let halgebra := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
    have htower : IsScalarTower A (X.presheaf.stalk x) F := functionField_isScalarTower X U ⟨x, hx⟩
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap A (X.presheaf.stalk x) a, (IsScalarTower.algebraMap_apply A _ F a).symm⟩
  · intro f hf
    have key : f ∈ (⨅ v : PrimeSpectrum A,
        Localization.subalgebra.ofField F _ v.asIdeal.primeCompl_le_nonZeroDivisors) := by
      refine Algebra.mem_iInf.mpr fun v => ?_
      have hxU : (hU.fromSpec v : X) ∈ U := by
        change (hU.fromSpec v : X) ∈ (U : Set X)
        rw [← hU.range_fromSpec]
        exact ⟨v, rfl⟩
      let halgebra := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec v, hxU⟩ : U)
      have htower : IsScalarTower A (X.presheaf.stalk (hU.fromSpec v : X)) F :=
        functionField_isScalarTower X U ⟨_, hxU⟩
      have hloc : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec v : X)) v.asIdeal :=
        hU.isLocalization_stalk' v hxU
      have hfx : f ∈ (algebraMap (X.presheaf.stalk (hU.fromSpec v : X)) F).range :=
        (Subring.mem_iInf.mp ((Subring.mem_iInf.mp hf) (hU.fromSpec v : X))) hxU
      obtain ⟨s, rfl⟩ := hfx
      obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl s
      refine ⟨a, t, t.2, ?_⟩
      have ht : algebraMap A F t ≠ 0 := by
        intro h0
        have : (t : A) = 0 := (IsFractionRing.injective A F) (by rw [h0, map_zero])
        exact t.2 (by rw [this]; exact v.asIdeal.zero_mem)
      rw [eq_mul_inv_iff_mul_eq₀ ht,
        IsScalarTower.algebraMap_apply A (X.presheaf.stalk (hU.fromSpec v : X)) F (t : A),
        ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply A (X.presheaf.stalk (hU.fromSpec v : X)) F a]
    rw [PrimeSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at key
    obtain ⟨a, rfl⟩ := key
    exact ⟨a, rfl⟩
end IsAffineOpen_range_algebraMap_functionField_eq_iInf
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
