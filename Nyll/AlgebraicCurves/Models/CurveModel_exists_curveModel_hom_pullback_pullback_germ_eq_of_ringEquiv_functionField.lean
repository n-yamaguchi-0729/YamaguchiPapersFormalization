/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
import Nyll.AlgebraicCurves.Models.CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv

/-!
# Curve Model exists curve Model hom pullback pullback germ eq of ring Equiv function Field
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

namespace CMTransport

theorem nonempty_preimage_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Y.Opens)
    [h : Nonempty (Scheme.Opens.toScheme U)] : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U)) := by
  obtain ⟨⟨y, hy⟩⟩ := h
  refine ⟨⟨(inv f).base y, ?_⟩⟩
  change f.base ((inv f).base y) ∈ (U : Set Y)
  have h1 : (inv f ≫ f).base y = y := by simp
  have h2 : (inv f ≫ f).base y = f.base ((inv f).base y) := Scheme.Hom.comp_apply _ _ _
  rw [← h2, h1]
  exact hy

end CMTransport

end CurveModel_exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField
end AlgebraicCurves.Models.Proofs

namespace AlgebraicCurve.CurveModel



open _root_.AlgebraicCurves.Models.Proofs in
open CurveModel_exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve in
open _root_.AlgebraicGeometry.SmoothProperCurve in
theorem exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField
    {R₀ : Type} [CommRing R₀] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀))
    [IsProper πX] [SmoothOfRelativeDimension 1 πX] [GeometricallyIntegral πX]
    {O : Type} [CommRing O] (j : R₀ →+* O) (k : Type) [Field k] [IsAlgClosed k] (i : O →+* k)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R₀))
    (hs : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j) = s)
    [AlgebraicGeometry.IsIntegral ↑(pullback πX s)]
    {L : Type} [Field L] [Algebra k L] (eL : L ≃+* ↥((pullback πX s).functionField))
    (heL : ∀ z : k, eL (algebraMap k L z) = baseToFunctionField (pullback.snd πX s) z) :
    ∃ (𝔐 : AlgebraicCurve.CurveModel k L)
      (e : 𝔐.C ⟶ pullback (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map
        (CommRingCat.ofHom i)))
      (_ : IsIso e),
      e ≫ pullback.snd (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map
        (CommRingCat.ofHom i)) = 𝔐.toBase ∧
      ∀ (U : X.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((pullback.fst πX s) ⁻¹ᵁ U))]
        [Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (pullback.snd πX (Spec.map
          (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫
          pullback.fst πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U))]
        (t : Γ(X, U)),
        𝔐.ffEquiv.symm (𝔐.C.germToFunctionField
          ((e ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map
            (CommRingCat.ofHom i)) ≫
            pullback.fst πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U)
          (((e ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map
            (CommRingCat.ofHom i)) ≫
            pullback.fst πX (Spec.map (CommRingCat.ofHom j))).app U).hom t)) =
        eL.symm ((pullback πX s).germToFunctionField ((pullback.fst πX s) ⁻¹ᵁ U) (((pullback.fst πX
          s).app U).hom t)) := by
  classical
  subst hs
  let : Algebra k ↥((pullback πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom
    j))).functionField) :=
    (baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map
      (CommRingCat.ofHom j)))).toAlgebra
  obtain ⟨_, _, 𝔐₁, e₁, he₁, hgerm₁⟩ :=
    exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
      R₀ πX k (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j))
  let eL' : ↥((pullback πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom
    j))).functionField) ≃ₐ[k] L :=
    AlgEquiv.ofRingEquiv (f := eL.symm) (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact (heL z).symm)
  obtain ⟨𝔐, f, hf, hgerm₂⟩ :=
    exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv eL' 𝔐₁
  let paste := pullbackLeftPullbackSndIso πX (Spec.map (CommRingCat.ofHom j)) (Spec.map
    (CommRingCat.ofHom i))
  refine ⟨𝔐, f.hom ≫ e₁.hom ≫ paste.inv, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, he₁, hf]
  · intro U _ _ _ t
    have hcomp : (f.hom ≫ e₁.hom ≫ paste.inv) ≫
        pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map
          (CommRingCat.ofHom i)) ≫
          pullback.fst πX (Spec.map (CommRingCat.ofHom j)) =
        f.hom ≫ e₁.hom ≫ pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map
          (CommRingCat.ofHom j)) := by
      simp only [Category.assoc, paste, pullbackLeftPullbackSndIso_inv_fst]
    have key : ∀ (g : 𝔐.C ⟶ X) (hg : g = f.hom ≫ e₁.hom ≫
        pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j)))
        [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ U))],
        𝔐.ffEquiv.symm (𝔐.C.germToFunctionField (g ⁻¹ᵁ U) ((g.app U).hom t)) =
          eL.symm ((pullback πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom
            j))).germToFunctionField
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j)))
              ⁻¹ᵁ U)
            (((pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom
              j))).app U).hom t)) := by
      intro g hg _
      subst hg
      set fst := pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j))
        with hfst
      set U₁ : (pullback πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom
        j))).Opens := fst ⁻¹ᵁ U with hU₁
      set V : 𝔐₁.C.Opens := e₁.hom ⁻¹ᵁ U₁ with hV
      have : Nonempty (Scheme.Opens.toScheme U₁) := inferInstance
      have hVne : Nonempty (Scheme.Opens.toScheme V) := CMTransport.nonempty_preimage_of_isIso
        e₁.hom U₁
      have hfVne : Nonempty (Scheme.Opens.toScheme (f.hom ⁻¹ᵁ V)) :=
        CMTransport.nonempty_preimage_of_isIso f.hom V
      have hstepA : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField ((f.hom ≫ e₁.hom ≫ fst) ⁻¹ᵁ U)
            (((f.hom ≫ e₁.hom ≫ fst).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField (f.hom ⁻¹ᵁ V)
            ((f.hom.app V).hom ((e₁.hom.app U₁).hom ((fst.app U).hom t)))) := by
        congr 1
      rw [hstepA, hgerm₂ V ((e₁.hom.app U₁).hom ((fst.app U).hom t)), hgerm₁ U₁ ((fst.app U).hom t)]
      rfl
    exact key _ hcomp
end AlgebraicCurve.CurveModel
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
