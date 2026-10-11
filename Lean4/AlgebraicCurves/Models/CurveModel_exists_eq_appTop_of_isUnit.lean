/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_eq_appTop_of_isUnit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Places.Rational.RationalFunctionField_exists_algebraMap_of_forall_ord_eq_zero

/-!
# Curve Model exists eq app Top of is Unit
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_exists_eq_appTop_of_isUnit

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem _root_.AlgebraicCurve.CurveModel.exists_eq_appTop_of_isUnit
    (k : Type u) [Field k] [IsAlgClosed k] (M : CurveModel k (RatFunc k))
    (u : Γ(M.C, ⊤)) (hu : IsUnit u) :
    ∃ c : k, u = M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  classical
  have : IsIntegral M.C := M.isIntegral
  obtain ⟨uu, rfl⟩ := hu
  let η := genericPoint M.C
  let γ : Γ(M.C, ⊤) →+* M.C.functionField := (M.C.presheaf.germ ⊤ η trivial).hom
  let g : RatFunc k := M.ffEquiv.symm (γ uu)
  have hg : g ≠ 0 := by
    have : IsUnit g := (Units.map (M.ffEquiv.symm.toRingHom.toMonoidHom.comp γ.toMonoidHom)
      uu).isUnit
    exact this.ne_zero
  have hord : ∀ v : Place k (RatFunc k), v.ord g = 0 := by
    intro v
    obtain ⟨x, rfl⟩ := M.placeOfPoint_bijective.2 v
    have hmem : ∀ w : Γ(M.C, ⊤)ˣ, M.ffEquiv.symm (γ w) ∈ (M.placeOfPoint x).toValuationSubring := by
      intro w
      have := M.range_stalk_eq x
      have hw : M.ffEquiv.symm (γ w) ∈ ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc
        k).toRingHom.comp
          (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)).range := by
        refine ⟨(M.C.presheaf.germ ⊤ x.1 trivial).hom w, ?_⟩
        have : Nonempty (⊤ : M.C.Opens) := ⟨⟨x.1, trivial⟩⟩
        exact congrArg M.ffEquiv.symm
          (M.C.algebraMap_germ_eq_germToFunctionField (U := ⊤)
            (show x.1 ∈ (⊤ : M.C.Opens) from trivial) (w : Γ(M.C, ⊤)))
      rw [this] at hw
      exact hw
    have h1 : g ∈ (M.placeOfPoint x).toValuationSubring := hmem uu
    have h2 : g⁻¹ ∈ (M.placeOfPoint x).toValuationSubring := by
      have := hmem uu⁻¹
      have hinv : M.ffEquiv.symm (γ ↑uu⁻¹) = g⁻¹ := by
        let ψ : Γ(M.C, ⊤) →+* RatFunc k := M.ffEquiv.symm.toRingHom.comp γ
        change ((Units.map ψ.toMonoidHom uu⁻¹ : (RatFunc k)ˣ) : RatFunc k) = ((Units.map
          ψ.toMonoidHom uu : (RatFunc k)ˣ) : RatFunc k)⁻¹
        rw [map_inv, Units.val_inv_eq_inv_val]
      rwa [hinv] at this
    let gu : (M.placeOfPoint x).toValuationSubringˣ :=
      ⟨⟨g, h1⟩, ⟨g⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hg), Subtype.ext (inv_mul_cancel₀ hg)⟩
    exact (M.placeOfPoint x).ord_coe_unit gu
  obtain ⟨c, -, hc⟩ := RationalFunctionField.exists_algebraMap_of_forall_ord_eq_zero hg hord
  refine ⟨c, ?_⟩
  apply AlgebraicGeometry.germ_injective_of_isIntegral M.C η (U := ⊤) trivial
  change γ uu = γ (M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
  have h3 : γ uu = M.ffEquiv (algebraMap k (RatFunc k) c) := by
    rw [← hc]; exact (M.ffEquiv.apply_symm_apply _).symm
  rw [h3, M.ffEquiv_algebraMap]
  rfl
end AlgebraicCurves.Models.Proofs.CurveModel_exists_eq_appTop_of_isUnit
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
