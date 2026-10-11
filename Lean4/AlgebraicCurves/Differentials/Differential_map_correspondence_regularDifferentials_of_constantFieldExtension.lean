/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Differentials.Basic
import AlgebraicCurves.FunctionFields.FinrankAlong_eq_and_trace_eq_of_constantFieldExtension
import AlgebraicCurves.Places.Place_exists_of_valuationSubring
import AlgebraicCurves.Places.Place_ord_diffCoeff_D_nonneg_of_perfectField
import AlgebraicCurves.Places.Place_exists_eq_smul_D_of_ord_ne_zero
import AlgebraicCurves.Places.Place_diffCoeff_smul_D_eq
import AlgebraicCurves.Places.Place_D_ne_zero_of_ord_ne_zero
import AlgebraicCurves.Places.Place_exists_ord_neg_of_transcendental
import AlgebraicCurves.Places.Place_transcendental_of_ord_ne_zero
import AlgebraicCurves.FunctionFields.FiniteDimensional_adjoin_of_transcendental
import AlgebraicCurves.Places.Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import AlgebraicCurves.FunctionFields.LinearIndependent_of_constantFieldExtension
import AlgebraicCurves.Cohomology.RiemannRoch.Genus_eq_of_constantFieldExtension_of_isAlgClosed
import AlgebraicCurves.Cohomology.RiemannRoch.Finite_and_finrank_regularDifferentials_eq_genus
import AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver
import AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import AlgebraicCurves.FunctionFields.SeparableAlong_of_charZero

/-!
# Differential map correspondence regular Differentials of constant Field Extension
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs
namespace Differential_map_correspondence_regularDifferentials_of_constantFieldExtension
open _root_.AlgebraicCurve.Place in
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  instAlgebra_restrictResidueField
  instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
attribute [-simp] AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

noncomputable section

open _root_.AlgebraicCurve
open _root_.KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace OmegaBaseChangeProof
open _root_.AlgebraicCurve

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_coe_nonneg (v : Place K F) (f : v.toValuationSubring) : 0 ≤ v.ord (f : F) := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hπ
  have : (f : F) = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    rw [hu, zpow_natCast]; push_cast; rfl
  rw [this, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ord_coe_nonneg v ⟨f, hf⟩

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem mem_of_ord_nonneg' (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  · exact mem_of_ord_nonneg v hf h

theorem exists_smul_D_eq_smul_dCoord [PerfectField K] [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (P : Place K F) {a t : F} (ha : a ∈ P.toValuationSubring) (ht : t ∈ P.toValuationSubring) :
    ∃ f ∈ P.toValuationSubring, a • D K F t = f • P.dCoord := by
  have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨π₀, hπ₀, hdc⟩ := P.exists_ord_eq_one_and_dCoord_eq
  have hπ₀' : P.ord π₀ ≠ 0 := by rw [hπ₀]; exact one_ne_zero
  obtain ⟨c, hc⟩ := AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero x P hπ₀' (D K F t)
  have hcoef : AlgebraicCurve.Place.diffCoeff π₀ (D K F t) = c := by
    rw [hc]
    exact AlgebraicCurve.Place.diffCoeff_smul_D_eq x P hπ₀' c
  have hord : 0 ≤ P.ord c := by
    rw [← hcoef]
    exact AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_perfectField x P hπ₀ (ord_nonneg_of_mem P
      ht)
  refine ⟨a * c, mul_mem ha (mem_of_ord_nonneg' P hord), ?_⟩
  rw [hc, hdc, smul_smul]

end PlaceFacts

end AlgebraicCurve.OmegaBaseChangeProof

end
end Differential_map_correspondence_regularDifferentials_of_constantFieldExtension
end AlgebraicCurves.Differentials.Proofs

namespace AlgebraicCurve.Differential

noncomputable section

open _root_.AlgebraicCurve _root_.KaehlerDifferential

open _root_.AlgebraicCurves.Differentials.Proofs in
open Differential_map_correspondence_regularDifferentials_of_constantFieldExtension in
open AlgebraicCurve.OmegaBaseChangeProof in
theorem map_correspondence_regularDifferentials_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [SMulCommClass E F FE] [IsAlgClosed E]
    [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE ψE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hφE : φE.toRingHom.IsIntegral) :
    (∀ ω : Ω[F⁄K], KaehlerDifferential.map K E F FE (Differential.correspondence φ ψ ω) =
        Differential.correspondence φE ψE (KaehlerDifferential.map K E F FE ω)) ∧
    Function.Injective (KaehlerDifferential.map K E F FE) ∧
    (∀ ω ∈ regularDifferentials K F,
        KaehlerDifferential.map K E F FE ω ∈ regularDifferentials E FE) ∧
    (∀ η ∈ regularDifferentials E FE,
        η ∈ Submodule.span E
          (KaehlerDifferential.map K E F FE '' (regularDifferentials K F : Set (Ω[F⁄K])))) := by
  classical
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have : CharZero FE := charZero_of_injective_algebraMap (algebraMap E FE).injective
  have : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  have : SMulCommClass E F' F'E := ⟨fun e f y => by simp only [Algebra.smul_def]; ring⟩
  set κ : Ω[F⁄K] →ₗ[F] Ω[FE⁄E] := KaehlerDifferential.map K E F FE with hκdef
  set κ' : Ω[F'⁄K] →ₗ[F'] Ω[F'E⁄E] := KaehlerDifferential.map K E F' F'E with hκ'def
  obtain ⟨x, hx, hxfin⟩ := hfg
  have := hxfin
  have hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F := ⟨x, hx, hxfin⟩
  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_ord_neg_of_transcendental x hx
  have hvx : v.ord x ≠ 0 := hv.ne
  have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  set x' : FE := algebraMap F FE x with hx'def
  obtain ⟨P₁, -, hP₁ord, -⟩ :=
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE hfg hfgE
      hgen v
  have hP₁x : P₁.ord x' ≠ 0 := by rw [hx'def, hP₁ord]; exact hvx
  have hx' : Transcendental E x' := AlgebraicCurve.Place.transcendental_of_ord_ne_zero P₁ hP₁x
  obtain ⟨y, hy, hyfin⟩ := hfgE
  have hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE := ⟨y, hy, hyfin⟩
  have := hyfin
  have hx'fin : FiniteDimensional (IntermediateField.adjoin E ({x'} : Set FE)) FE :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental y hx'
  have : Algebra.IsAlgebraic (IntermediateField.adjoin E ({x'} : Set FE)) FE :=
    Algebra.IsAlgebraic.of_finite _ _
  have hDx' : D E FE x' ≠ 0 := AlgebraicCurve.Place.D_ne_zero_of_ord_ne_zero x' P₁ hP₁x
  have hrep : ∀ ω : Ω[F⁄K], ∃ g : F, ω = g • D K F x := fun ω =>
    AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero x v hvx ω
  have hκ : ∀ g : F, κ (g • D K F x) = algebraMap F FE g • D E FE x' := fun g => by
    rw [LinearMap.map_smul, hκdef, KaehlerDifferential.map_D, algebraMap_smul]
  have hκ' : ∀ (g t : F'), κ' (g • D K F' t) = algebraMap F' F'E g • D E F'E (algebraMap F' F'E t)
    :=
    fun g t => by rw [LinearMap.map_smul, hκ'def, KaehlerDifferential.map_D, algebraMap_smul]
  have hinj : Function.Injective κ := by
    intro ω₁ ω₂ h
    obtain ⟨g₁, rfl⟩ := hrep ω₁
    obtain ⟨g₂, rfl⟩ := hrep ω₂
    rw [hκ, hκ] at h
    have h' : (algebraMap F FE g₁ - algebraMap F FE g₂) • D E FE x' = 0 := by
      rw [sub_smul, h, sub_self]
    have h'' : algebraMap F FE g₁ = algebraMap F FE g₂ :=
      sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hDx')
    rw [(algebraMap F FE).injective h'']
  have hreg : ∀ ω ∈ regularDifferentials K F, κ ω ∈ regularDifferentials E FE := by
    intro ω hω
    rw [mem_regularDifferentials_iff]
    intro P
    by_cases hall : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring
    · obtain ⟨g, rfl⟩ := hrep ω
      rw [hκ]
      exact exists_smul_D_eq_smul_dCoord x' P (hall g) (hall x)
    · set A : ValuationSubring F := P.toValuationSubring.comap (algebraMap F FE) with hAdef
      have hAK : ∀ a : K, algebraMap K F a ∈ A := fun a => by
        change algebraMap F FE (algebraMap K F a) ∈ P.toValuationSubring
        rw [← IsScalarTower.algebraMap_apply K F FE a, IsScalarTower.algebraMap_apply K E FE a]
        exact P.algebraMap_mem' _
      have hA : A ≠ ⊤ := by
        intro htop
        exact hall fun f => (show f ∈ A from htop ▸ trivial)
      obtain ⟨v', hv'⟩ := AlgebraicCurve.Place.exists_of_valuationSubring x A hAK hA
      obtain ⟨h, hh, hωh⟩ := (mem_regularDifferentials_iff (K := K) (F := F)).1 hω v'
      obtain ⟨πv, hπv, hdcv⟩ := v'.exists_ord_eq_one_and_dCoord_eq
      have hπvmem : πv ∈ v'.toValuationSubring :=
        mem_of_ord_nonneg' v' (by rw [hπv]; exact zero_le_one)
      have hh' : algebraMap F FE h ∈ P.toValuationSubring := by
        have : h ∈ A := by rw [hv'] at hh; exact hh
        exact this
      have hπv' : algebraMap F FE πv ∈ P.toValuationSubring := by
        have : πv ∈ A := by rw [hv'] at hπvmem; exact hπvmem
        exact this
      rw [hωh, hdcv, LinearMap.map_smul, hκdef, KaehlerDifferential.map_D,
        ← algebraMap_smul FE h (D E FE (algebraMap F FE πv))]
      exact exists_smul_D_eq_smul_dCoord x' P hh' hπv'
  have hspan : ∀ η ∈ regularDifferentials E FE,
      η ∈ Submodule.span E (κ '' (regularDifferentials K F : Set (Ω[F⁄K]))) := by
    have : Algebra.EssFiniteType K F :=
      AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hxfin
    have : HasCanonicalDivisor (K := K) (F := F) :=
      AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := K) (F := F)
    have : Algebra.EssFiniteType E FE :=
      AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hy hyfin
    have : HasCanonicalDivisor (K := E) (F := FE) :=
      AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := E) (F := FE)
    obtain ⟨hfinK, hrankK⟩ :=
      AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)
    obtain ⟨hfinE, hrankE⟩ :=
      AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := E) (F := FE)
    have hgenus : genus E FE = genus K F :=
      AlgebraicCurve.genus_eq_of_constantFieldExtension_of_isAlgClosed K F E FE hfg hfgE hgen
    have := hfinK
    have := hfinE
    set bK := Module.finBasis K ↥(regularDifferentials K F) with hbK
    choose f hf using fun i => hrep (bK i : Ω[F⁄K])
    have hfli : LinearIndependent K f := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hsum : ((∑ j, c j • bK j : ↥(regularDifferentials K F)) : Ω[F⁄K]) = 0 := by
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul, hf, ← smul_assoc, ← Finset.sum_smul]
        rw [show (∑ j, c j • f j) = 0 from hc, zero_smul]
      have h0 : ∑ j, c j • bK j = 0 := Subtype.ext (by simpa using hsum)
      exact Fintype.linearIndependent_iff.1 bK.linearIndependent c h0 i
    have hfli' : LinearIndependent E (fun i => algebraMap F FE (f i)) :=
      AlgebraicCurve.linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen hfli
    set w : Fin (Module.finrank K ↥(regularDifferentials K F)) → Ω[FE⁄E] :=
      fun i => κ (bK i : Ω[F⁄K]) with hw
    have hw' : ∀ i, w i = algebraMap F FE (f i) • D E FE x' := fun i => by
      simp only [hw]; rw [hf i, hκ]
    have hwli : LinearIndependent E w := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hsum : (∑ j, c j • algebraMap F FE (f j)) • D E FE x' = 0 := by
        rw [Finset.sum_smul]
        simp only [smul_assoc]
        simpa only [hw'] using hc
      have h0 := (smul_eq_zero.1 hsum).resolve_right hDx'
      exact Fintype.linearIndependent_iff.1 hfli' c h0 i
    have hwmem : ∀ i, w i ∈ regularDifferentials E FE := fun i => hreg _ (bK i).2
    set W : Submodule E (Ω[FE⁄E]) := Submodule.span E (Set.range w) with hW
    have hWle : W ≤ regularDifferentials E FE :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hwmem i)
    have hWrank : Module.finrank E W = Module.finrank E ↥(regularDifferentials E FE) := by
      rw [hW, finrank_span_eq_card hwli, Fintype.card_fin, hrankE, hgenus, ← hrankK]
    have hWeq : W = regularDifferentials E FE := Submodule.eq_of_le_of_finrank_eq hWle hWrank
    intro η hη
    have hηW : η ∈ W := by rw [hWeq]; exact hη
    refine Submodule.span_mono ?_ hηW
    rintro _ ⟨i, rfl⟩
    exact ⟨bK i, (bK i).2, rfl⟩
  have hint : ∀ ω : Ω[F⁄K],
      κ (Differential.correspondence φ ψ ω) = Differential.correspondence φE ψE (κ ω) := by
    obtain ⟨hfinφ, hfinφE, -, htr⟩ :=
      AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension K F hfg F' hfg' φ hφ
        E FE hfgE hgen F'E hfgE' hgen' φE hφcomm hφE
    have hsep : SeparableAlong K φ := AlgebraicCurve.separableAlong_of_charZero φ hφ
    have hsepE : SeparableAlong E φE := AlgebraicCurve.separableAlong_of_charZero φE hφE
    have hpull : ∀ (σ : F →ₐ[K] F') (σE : FE →ₐ[E] F'E),
        (∀ f : F, σE (algebraMap F FE f) = algebraMap F' F'E (σ f)) →
        ∀ ω : Ω[F⁄K], κ' (Differential.pullbackAlong σ ω) = Differential.pullbackAlong σE (κ ω) :=
          by
      intro σ σE hcomm ω
      obtain ⟨g, rfl⟩ := hrep ω
      rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_D, hκ', hκ,
        Differential.pullbackAlong_smul, Differential.pullbackAlong_D, hcomm, hx'def, hcomm]
    have hφx : Transcendental K (φ x) := fun h =>
      hx ((isAlgebraic_algHom_iff φ φ.toRingHom.injective).mp h)
    obtain ⟨x₁, hx₁, hx₁fin⟩ := hfg'
    have := hx₁fin
    have : FiniteDimensional (IntermediateField.adjoin K ({φ x} : Set F')) F' :=
      AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x₁ hφx
    have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({φ x} : Set F')) F' :=
      Algebra.IsAlgebraic.of_finite _ _
    obtain ⟨v₁, hv₁⟩ := AlgebraicCurve.Place.exists_ord_neg_of_transcendental (φ x) hφx
    have hrep' : ∀ η : Ω[F'⁄K], ∃ u : F', η = u • D K F' (φ x) := fun η =>
      AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero (φ x) v₁ hv₁.ne η
    intro ω
    obtain ⟨u, hu⟩ := hrep' (Differential.pullbackAlong ψ ω)
    rw [Differential.correspondence_apply, Differential.correspondence_apply, hu,
      ← Differential.pullbackAlong_D, Differential.traceAlong_smul_pullbackAlong φ hsep u, hκ]
    rw [← hpull ψ ψE hψcomm, hu, hκ']
    have hDφ : D E F'E (algebraMap F' F'E (φ x)) = Differential.pullbackAlong φE (D E FE x') := by
      rw [Differential.pullbackAlong_D, hx'def, hφcomm]
    rw [hDφ, Differential.traceAlong_smul_pullbackAlong φE hsepE, htr u, algebraMap_smul]
  exact ⟨hint, hinj, hreg, hspan⟩
end
end AlgebraicCurve.Differential
end ProofImplementation
