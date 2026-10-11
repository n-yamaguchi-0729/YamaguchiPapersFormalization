/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_not_isAffine_of_isProper_of_isCurveOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-!
# Not is Affine of is Proper of is Curve Over
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.Not_isAffine_of_isProper_of_isCurveOver

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem _root_.AlgebraicCurve.not_isAffine_of_isProper_of_isCurveOver
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField) :
    ¬ IsAffine C := by
  intro hA
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have hΓ : IsField Γ(C, ⊤) := isField_of_universallyClosed k c
  let φ : k →+* Γ(C, ⊤) := c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hφint : φ.IsIntegral := by
    have h1 : c.appTop.hom.IsIntegral := isIntegral_appTop_of_universallyClosed c
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.IsIntegral :=
      RingHom.isIntegral_of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of
        k)).commRingCatIsoToRingEquiv.symm.surjective
    exact RingHom.IsIntegral.trans _ _ h2 h1
  have hφsurj : Function.Surjective φ := by
    let := φ.toAlgebra
    have : Algebra.IsIntegral k Γ(C, ⊤) := ⟨hφint⟩
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(C, ⊤))).2
  have hgerm : Function.Surjective (C.presheaf.germ ⊤ (genericPoint C) trivial).hom := by
    let := C.presheaf.algebra_section_stalk (⟨genericPoint C, trivial⟩ : (⊤ : C.Opens))
    have hloc := (isAffineOpen_top C).isLocalization_stalk ⟨genericPoint C, trivial⟩
    have h0 : (0 : Γ(C, ⊤)) ∉ ((isAffineOpen_top C).primeIdealOf ⟨genericPoint C,
      trivial⟩).asIdeal.primeCompl :=
      fun h => h (Ideal.zero_mem _)
    exact (IsField.localization_map_bijective h0 hΓ).2
  have hsurj : Function.Surjective (algebraMap k C.functionField) := by
    change Function.Surjective ((C.presheaf.germ ⊤ (genericPoint C) trivial).hom.comp φ)
    exact hgerm.comp hφsurj
  have hΩ : Subsingleton Ω[C.functionField⁄k] := by
    refine ⟨fun a b => ?_⟩
    have hzero : ∀ x : Ω[C.functionField⁄k], x = 0 := by
      intro x
      have hx : x ∈ Submodule.span C.functionField (Set.range (KaehlerDifferential.D k
        C.functionField)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨s, rfl⟩
        obtain ⟨r, rfl⟩ := hsurj s
        exact Derivation.map_algebraMap _ r
      · rfl
      · intro _ _ _ _ h1 h2; rw [h1, h2, add_zero]
      · intro _ _ _ h; rw [h, smul_zero]
    rw [hzero a, hzero b]
  have h1 := hK.kaehler_free_rank_one.2
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1
end AlgebraicCurves.Models.Proofs.Not_isAffine_of_isProper_of_isCurveOver
end ProofImplementation
