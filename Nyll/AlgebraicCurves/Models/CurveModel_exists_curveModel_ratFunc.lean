/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_curveModel_ratFunc.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Construction
import Nyll.AlgebraicCurves.Models.CurveModel_isProper_smooth_places_affineCover_glued

import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Curve Model exists curve Model rat Func
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_exists_curveModel_ratFunc

noncomputable section

open CategoryTheory AlgebraicGeometry IntermediateField

universe u

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

section InstanceFacts

variable (κ : Type u) [Field κ]

theorem ratFunc_transcendental_X : Transcendental κ (RatFunc.X : RatFunc κ) :=
  RatFunc.transcendental_X

theorem ratFunc_adjoin_X_eq_top : κ⟮(RatFunc.X : RatFunc κ)⟯ = ⊤ := RatFunc.adjoin_X

theorem mem_ratFunc_adjoin_X (f : RatFunc κ) : f ∈ κ⟮(RatFunc.X : RatFunc κ)⟯ := by
  rw [ratFunc_adjoin_X_eq_top]; trivial

scoped instance ratFunc_finiteDimensional_adjoin_X :
    FiniteDimensional κ⟮(RatFunc.X : RatFunc κ)⟯ (RatFunc κ) := by
  refine ⟨⟨{1}, Submodule.eq_top_iff'.mpr fun f => ?_⟩⟩
  rw [Finset.coe_singleton]
  have hf : f = (⟨f, mem_ratFunc_adjoin_X κ f⟩ : κ⟮(RatFunc.X : RatFunc κ)⟯) • (1 : RatFunc κ) := by
    rw [IntermediateField.smul_def, smul_eq_mul, mul_one]
  rw [hf]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self 1)

scoped instance ratFunc_isSeparable_adjoin_X :
    Algebra.IsSeparable κ⟮(RatFunc.X : RatFunc κ)⟯ (RatFunc κ) :=
  ⟨fun f => by
    have hf : f = algebraMap κ⟮(RatFunc.X : RatFunc κ)⟯ (RatFunc κ) ⟨f, mem_ratFunc_adjoin_X κ f⟩ :=
      rfl
    rw [hf]
    exact isSeparable_algebraMap _⟩

end InstanceFacts

section Model

variable (κ : Type u) [Field κ] [IsAlgClosed κ] [Fact ((RatFunc.X : RatFunc κ) ≠ 0)]

theorem ratFunc_isProper_smooth_places_affineCover_glued :
    IsProper (CurveModel.gluedToBase κ (RatFunc.X : RatFunc κ)) ∧
    SmoothOfRelativeDimension 1 (CurveModel.gluedToBase κ (RatFunc.X : RatFunc κ)) ∧
    (∃ P : closedPoints (CurveModel.glued κ (RatFunc.X : RatFunc κ)) → Place κ (RatFunc κ),
      Function.Bijective P ∧
      ∀ x : closedPoints (CurveModel.glued κ (RatFunc.X : RatFunc κ)),
        (((CurveModel.gluedFunctionFieldEquiv κ (RatFunc.X : RatFunc κ)).symm :
              (CurveModel.glued κ (RatFunc.X : RatFunc κ)).functionField ≃+* RatFunc
                κ).toRingHom.comp
            (algebraMap ((CurveModel.glued κ (RatFunc.X : RatFunc κ)).presheaf.stalk x.1)
              (CurveModel.glued κ (RatFunc.X : RatFunc κ)).functionField)).range =
          (P x).toValuationSubring.toSubring) ∧
    (∀ F : Finset (CurveModel.glued κ (RatFunc.X : RatFunc κ)),
      ∃ U : (CurveModel.glued κ (RatFunc.X : RatFunc κ)).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :=
  CurveModel.isProper_smooth_places_affineCover_glued κ (RatFunc.X : RatFunc κ)
    (ratFunc_transcendental_X κ)

scoped instance ratFunc_isProper_gluedToBase :
    IsProper (CurveModel.gluedToBase κ (RatFunc.X : RatFunc κ)) :=
  (ratFunc_isProper_smooth_places_affineCover_glued κ).1

scoped instance ratFunc_smoothOfRelativeDimension_one_gluedToBase :
    SmoothOfRelativeDimension 1 (CurveModel.gluedToBase κ (RatFunc.X : RatFunc κ)) :=
  (ratFunc_isProper_smooth_places_affineCover_glued κ).2.1

/-- The smooth proper curve model of the rational function field assembled from the two affine
charts associated to `RatFunc.X`. -/
def ratFuncCurveModel : CurveModel κ (RatFunc κ) where
  C := CurveModel.glued κ (RatFunc.X : RatFunc κ)
  toBase := CurveModel.gluedToBase κ (RatFunc.X : RatFunc κ)
  ffEquiv := CurveModel.gluedFunctionFieldEquiv κ (RatFunc.X : RatFunc κ)
  ffEquiv_algebraMap := CurveModel.gluedFunctionFieldEquiv_algebraMap κ (RatFunc.X : RatFunc κ)
  placeOfPoint := (ratFunc_isProper_smooth_places_affineCover_glued κ).2.2.1.choose
  placeOfPoint_bijective := (ratFunc_isProper_smooth_places_affineCover_glued κ).2.2.1.choose_spec.1
  range_stalk_eq := (ratFunc_isProper_smooth_places_affineCover_glued κ).2.2.1.choose_spec.2
  finset_subset_affineOpen := (ratFunc_isProper_smooth_places_affineCover_glued κ).2.2.2
@[scoped simp]
theorem ratFuncCurveModel_C :
    (ratFuncCurveModel κ).C = CurveModel.glued κ (RatFunc.X : RatFunc κ) := rfl

theorem ratFuncCurveModel_toBase :
    (ratFuncCurveModel κ).toBase = CurveModel.gluedToBase κ (RatFunc.X : RatFunc κ) := rfl

theorem ratFuncCurveModel_ffEquiv :
    (ratFuncCurveModel κ).ffEquiv = CurveModel.gluedFunctionFieldEquiv κ (RatFunc.X : RatFunc κ) :=
  rfl

end Model

end AlgebraicCurve

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.CurveModel.exists_curveModel_ratFunc
    (κ : Type u) [Field κ] [IsAlgClosed κ] [Fact ((RatFunc.X : RatFunc κ) ≠ 0)] :
    ∃ (M : CurveModel κ (RatFunc κ)) (e : M.C ≅ CurveModel.glued κ (RatFunc.X : RatFunc κ)),
      e.hom ≫ CurveModel.gluedToBase κ (RatFunc.X : RatFunc κ) = M.toBase :=
  ⟨CurveModel_exists_curveModel_ratFunc.AlgebraicCurve.ratFuncCurveModel κ,
    Iso.refl _, Category.id_comp _⟩

end
end AlgebraicCurves.Models.Proofs.CurveModel_exists_curveModel_ratFunc
end ProofImplementation
