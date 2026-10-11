/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Differentials.Kaehler.Weil
import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Differentials.WeilOfKaehler_ne_zero_and_maximal
import AlgebraicCurves.Cohomology.RiemannRoch.WeilOfKaehler_mem_omegaSpace_of_residueTheorem
import AlgebraicCurves.Differentials.WeilDifferentialRankOne_of_isCurveOver

/-!
# Exists linear Equiv regular Differentials omega Space zero
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsEquivRegularDifferentials
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
attribute [-simp] AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_vs {f : F} (hf : f ∈
  v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [v.ord_zero]
  · have hle : v.adicValuation f ≤ 1 := by
      rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    have hlog : WithZero.log (v.adicValuation f) ≤ 0 := by
      rw [← WithZero.exp_zero] at hle
      exact (WithZero.log_le_iff_le_exp (v.adicValuation_ne_zero hf0)).mpr hle
    unfold Place.ord
    omega

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.mem_vs_of_ord_nonneg {f : F} (h : 0 ≤ v.ord f) : f ∈
  v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

open _root_.AlgebraicCurve.Place
variable [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_add_s2 (ω η : Ω[F⁄K]) :
    v.differentialCoeff (ω + η) = v.differentialCoeff ω + v.differentialCoeff η :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.differentialCoeff_smul_algebraMap_s2 (c : K) (ω :
  Ω[F⁄K]) :
    v.differentialCoeff (c • ω) = algebraMap K F c * v.differentialCoeff ω := by
  rw [← v.differentialCoeff_smul, algebraMap_smul]

open _root_.AlgebraicCurve.Place
end Place

theorem hasSeparableResidue_of_perfectField [PerfectField K] [∀ v : Place K F, v.FiniteResidue] :
    HasSeparableResidue K F where
  trace_ne_zero v :=
    haveI : Module.Finite K v.ResidueField := Place.FiniteResidue.finite
    Algebra.trace_ne_zero K v.ResidueField

theorem nonempty_place_of_constantsAreBase [Nontrivial Ω[F⁄K]] (hC : ConstantsAreBase K F) :
    Nonempty (Place K F) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsurj : Function.Surjective (algebraMap K F) := fun f => by
    have hf : f ∈ LSpace (0 : Divisor K F) := fun v => (IsEmpty.false v).elim
    rw [hC] at hf
    obtain ⟨c, hc⟩ := hf
    exact ⟨c, hc⟩
  have hrange : ∀ x ∈ Set.range (KaehlerDifferential.D K F), (x : Ω[F⁄K]) = 0 := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨c, rfl⟩ := hsurj f
    exact Derivation.map_algebraMap _ c
  have htop : (⊤ : Submodule F Ω[F⁄K]) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    exact hrange
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[F⁄K])
  have : x ∈ (⊥ : Submodule F Ω[F⁄K]) := htop ▸ Submodule.mem_top
  exact hx ((Submodule.mem_bot F).mp this)

section Generic

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

omit [HasCanonicalLocalResidueKStar K F] in
theorem canonicalDivisorOf_nonneg_of_mem_regularDifferentials {ω : Ω[F⁄K]} (hω0 : ω ≠ 0)
    (hω : ω ∈ regularDifferentials K F) : 0 ≤ canonicalDivisorOf hω0 := by
  refine Finsupp.le_def.mpr fun v => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, canonicalDivisorOf_apply]
  obtain ⟨g, hg, hωg⟩ := hω v
  change 0 ≤ v.ord (v.differentialCoeff ω)
  rw [v.differentialCoeff_unique hωg]
  exact v.ord_nonneg_of_mem_vs hg

omit [HasCanonicalLocalResidueKStar K F] [Nontrivial Ω[F⁄K]] in
theorem mem_regularDifferentials_of_canonicalDivisorOf_nonneg {ω : Ω[F⁄K]} (hω0 : ω ≠ 0)
    (h : 0 ≤ canonicalDivisorOf hω0) : ω ∈ regularDifferentials K F := by
  intro v
  refine ⟨v.differentialCoeff ω, ?_, (v.differentialCoeff_smul_dCoord ω).symm⟩
  apply v.mem_vs_of_ord_nonneg
  have hv := Finsupp.le_def.mp h v
  rw [Finsupp.coe_zero, Pi.zero_apply, canonicalDivisorOf_apply] at hv
  exact hv

omit [HasCanonicalDivisor (K := K) (F := F)] in
theorem kaehlerResidueTerm_add_left_s2 (ω η : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (ω + η) α v = kaehlerResidueTerm ω α v + kaehlerResidueTerm η α v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_add_s2, mul_add, map_add, map_add]

omit [HasCanonicalDivisor (K := K) (F := F)] in
theorem kaehlerResidueTerm_smul_left_s2 (c : K) (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (c • ω) α v = c * kaehlerResidueTerm ω α v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul_algebraMap_s2, mul_left_comm, ← Algebra.smul_def, map_smul, map_smul,
    smul_eq_mul]

omit [HasCanonicalDivisor (K := K) (F := F)] in
theorem kaehlerResidueTerm_zero_left_s2 (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (0 : Ω[F⁄K]) α v = 0 :=
  kaehlerResidueTerm_eq_zero_of_ord_nonneg (Or.inl (by rw [v.differentialCoeff_zero, mul_zero]))

omit [HasCanonicalDivisor (K := K) (F := F)] in
theorem kaehlerResidueTerm_fsmul_left (f : F) (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (f • ω) α v = kaehlerResidueTerm ω (mulAdele K f α) v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul, mulAdele_apply, mul_left_comm, mul_assoc]

variable [HasPrincipalDivisors K F]

omit [HasPrincipalDivisors K F] in
theorem kaehlerResidueTerm_support_finite_of_adeleSpace' (ω : Ω[F⁄K]) (α : adeleSpace K F) :
    (Function.support (kaehlerResidueTerm ω (α : Place K F → F))).Finite := by
  rcases eq_or_ne ω 0 with rfl | hω
  · refine Set.Finite.subset Set.finite_empty fun v hv => ?_
    exact hv (kaehlerResidueTerm_zero_left_s2 _ v)
  · exact kaehlerResidueTerm_support_finite_of_adeleSpace hω α.2

/-- The adelic linear functional obtained by summing residues against a differential. -/
noncomputable def kaehlerToWeil (ω : Ω[F⁄K]) : Module.Dual K (adeleSpace K F) where
  toFun α := ∑ᶠ v, kaehlerResidueTerm ω (α : Place K F → F) v
  map_add' α β := by
    rw [← finsum_add_distrib (kaehlerResidueTerm_support_finite_of_adeleSpace' ω α)
      (kaehlerResidueTerm_support_finite_of_adeleSpace' ω β)]
    refine finsum_congr fun v => ?_
    unfold kaehlerResidueTerm
    rw [Submodule.coe_add, Pi.add_apply, add_mul, map_add, map_add]
  map_smul' c α := by
    simp only [RingHom.id_apply]
    rw [smul_finsum]
    refine finsum_congr fun v => ?_
    unfold kaehlerResidueTerm
    rw [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, mul_assoc,
      ← Algebra.smul_def, map_smul, map_smul]

omit [HasPrincipalDivisors K F] in
theorem kaehlerToWeil_apply (ω : Ω[F⁄K]) (α : adeleSpace K F) :
    kaehlerToWeil ω α = ∑ᶠ v, kaehlerResidueTerm ω (α : Place K F → F) v := rfl

omit [HasPrincipalDivisors K F] in
theorem kaehlerToWeil_eq_weilOfKaehler {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    kaehlerToWeil ω = weilOfKaehler K F hω :=
  LinearMap.ext fun _ => rfl

omit [HasPrincipalDivisors K F] in
theorem kaehlerToWeil_zero : kaehlerToWeil (0 : Ω[F⁄K]) = (0 : Module.Dual K (adeleSpace K F)) :=
  LinearMap.ext fun _α => finsum_eq_zero_of_forall_eq_zero fun v =>
    kaehlerResidueTerm_zero_left_s2 _ v

omit [HasPrincipalDivisors K F] in
theorem kaehlerToWeil_add (ω η : Ω[F⁄K]) :
    kaehlerToWeil (ω + η) = (kaehlerToWeil ω + kaehlerToWeil η : Module.Dual K (adeleSpace K F))
      := by
  refine LinearMap.ext fun α => ?_
  rw [LinearMap.add_apply, kaehlerToWeil_apply, kaehlerToWeil_apply, kaehlerToWeil_apply,
    ← finsum_add_distrib (kaehlerResidueTerm_support_finite_of_adeleSpace' ω α)
      (kaehlerResidueTerm_support_finite_of_adeleSpace' η α)]
  exact finsum_congr fun v => kaehlerResidueTerm_add_left_s2 ω η _ v

omit [HasPrincipalDivisors K F] in
theorem kaehlerToWeil_smul (c : K) (ω : Ω[F⁄K]) :
    kaehlerToWeil (c • ω) = (c • kaehlerToWeil ω : Module.Dual K (adeleSpace K F)) := by
  refine LinearMap.ext fun α => ?_
  rw [LinearMap.smul_apply, kaehlerToWeil_apply, kaehlerToWeil_apply, smul_finsum]
  exact finsum_congr fun v => by rw [kaehlerResidueTerm_smul_left_s2, smul_eq_mul]

theorem weilSmul_kaehlerToWeil (f : F) (ω : Ω[F⁄K]) :
    weilSmul K F f (kaehlerToWeil ω) = kaehlerToWeil (f • ω) := by
  refine LinearMap.ext fun α => ?_
  rw [weilSmul_apply, kaehlerToWeil_apply, kaehlerToWeil_apply, adeleSpaceMul_coe]
  exact finsum_congr fun v => (kaehlerResidueTerm_fsmul_left f ω _ v).symm

/-- The linear map from differentials to adelic residue functionals. -/
noncomputable def kaehlerToWeilLinear : Ω[F⁄K] →ₗ[K] Module.Dual K (adeleSpace K F) where
  toFun := kaehlerToWeil
  map_add' := kaehlerToWeil_add
  map_smul' c ω := by rw [RingHom.id_apply, kaehlerToWeil_smul]

theorem kaehlerToWeil_mem_omegaSpace_zero (hRT : ResidueTheorem K F) {ω : Ω[F⁄K]}
    (hω : ω ∈ regularDifferentials K F) :
    kaehlerToWeil ω ∈ omegaSpace (K := K) (F := F) (0 : Divisor K F) := by
  rcases eq_or_ne ω 0 with rfl | h0
  · rw [kaehlerToWeil_zero]
    exact Submodule.zero_mem _
  · rw [kaehlerToWeil_eq_weilOfKaehler h0]
    exact omegaSpace_antitone (canonicalDivisorOf_nonneg_of_mem_regularDifferentials h0 hω)
      (weilOfKaehler_mem_omegaSpace_of_residueTheorem hRT h0)

/-- Map regular differentials to Weil differentials vanishing on the zero-divisor subspace. -/
noncomputable def regularToOmega (hRT : ResidueTheorem K F) :
    ↥(regularDifferentials K F) →ₗ[K] ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)) :=
  LinearMap.codRestrict (omegaSpace (K := K) (F := F) (0 : Divisor K F))
    (kaehlerToWeilLinear.comp (regularDifferentials K F).subtype)
    (fun ω => kaehlerToWeil_mem_omegaSpace_zero hRT ω.2)

theorem coe_regularToOmega_apply (hRT : ResidueTheorem K F) (ω : ↥(regularDifferentials K F)) :
    ((regularToOmega hRT ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)))
      : Module.Dual K (adeleSpace K F)) = kaehlerToWeil (ω : Ω[F⁄K]) := rfl

end Generic

theorem exists_linearEquiv_regularDifferentials_omegaSpace_zero' {K : Type*} {F : Type*}
    [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F) :
    ∃ e : ↥(regularDifferentials K F) ≃ₗ[K] ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)),
      ∀ (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0),
        ((e ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F))) : Module.Dual K ↥(adeleSpace K
          F))
          = weilOfKaehler K F hω := by
  have : HasSeparableResidue K F := hasSeparableResidue_of_perfectField
  have : Nonempty (Place K F) := nonempty_place_of_constantsAreBase hC
  have hinj : Function.Injective (regularToOmega (K := K) (F := F) hRT) := by
    intro ω η h
    apply Subtype.ext
    by_contra hne
    have hne' : (ω : Ω[F⁄K]) - (η : Ω[F⁄K]) ≠ 0 := sub_ne_zero.mpr hne
    have hval := congrArg (fun x : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)) =>
      (x : Module.Dual K (adeleSpace K F))) h
    simp only [coe_regularToOmega_apply] at hval
    have hzero : kaehlerToWeil ((ω : Ω[F⁄K]) - (η : Ω[F⁄K])) = (0 : Module.Dual K (adeleSpace K
      F)) := by
      rw [sub_eq_add_neg, kaehlerToWeil_add, ← neg_one_smul K (η : Ω[F⁄K]), kaehlerToWeil_smul,
        hval, neg_one_smul K (kaehlerToWeil (η : Ω[F⁄K])), add_neg_cancel]
    rw [kaehlerToWeil_eq_weilOfKaehler hne'] at hzero
    exact (weilOfKaehler_ne_zero_and_maximal hne').1 hzero
  have hsurj : Function.Surjective (regularToOmega (K := K) (F := F) hRT) := by
    rintro ⟨μ, hμ⟩
    rcases eq_or_ne μ 0 with rfl | hμ0
    · exact ⟨0, Subtype.ext
        (by rw [coe_regularToOmega_apply, Submodule.coe_zero, kaehlerToWeil_zero])⟩
    obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
    have hmax := weilOfKaehler_ne_zero_and_maximal (K := K) (F := F) hω₀
    have hlmem : weilOfKaehler K F hω₀ ∈ weilDifferentialModule K F :=
      omegaSpace_le_weilDifferentialModule _ (weilOfKaehler_mem_omegaSpace_of_residueTheorem hRT
        hω₀)
    have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule _ hμ
    obtain ⟨f, hf, -⟩ := weilDifferentialRankOne_of_isCurveOver (K := K) (F := F) hC hlmem hmax.1
      hμmem
    have hf0 : f ≠ 0 := by
      rintro rfl
      apply hμ0
      rw [hf]
      refine LinearMap.ext fun α => ?_
      rw [weilSmul_apply, LinearMap.zero_apply]
      have : adeleSpaceMul K F (0 : F) α = 0 :=
        Subtype.ext (funext fun v => by rw [adeleSpaceMul_coe, mulAdele_apply, zero_mul]; rfl)
      rw [this, map_zero]
    have hfω : f • ω₀ ≠ 0 := smul_ne_zero hf0 hω₀
    have hμ' : μ = kaehlerToWeil (f • ω₀) := by
      rw [hf, ← kaehlerToWeil_eq_weilOfKaehler hω₀, weilSmul_kaehlerToWeil]
    have hreg : f • ω₀ ∈ regularDifferentials K F := by
      refine mem_regularDifferentials_of_canonicalDivisorOf_nonneg hfω ?_
      refine (weilOfKaehler_ne_zero_and_maximal hfω).2 0 ?_
      rw [← kaehlerToWeil_eq_weilOfKaehler hfω, ← hμ']
      exact hμ
    exact ⟨⟨f • ω₀, hreg⟩, Subtype.ext (by rw [coe_regularToOmega_apply, ← hμ'])⟩
  refine ⟨LinearEquiv.ofBijective (regularToOmega hRT) ⟨hinj, hsurj⟩, fun ω hω => ?_⟩
  change kaehlerToWeil (ω : Ω[F⁄K]) = weilOfKaehler K F hω
  exact kaehlerToWeil_eq_weilOfKaehler hω

end AlgebraicCurve

open _root_.AlgebraicCurve AlgebraicCurve in
theorem _root_.AlgebraicCurve.exists_linearEquiv_regularDifferentials_omegaSpace_zero {K : Type*}
  {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F) :
    ∃ e : ↥(regularDifferentials K F) ≃ₗ[K] ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)),
      ∀ (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0),
        ((e ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F))) : Module.Dual K ↥(adeleSpace K
          F))
          = weilOfKaehler K F hω :=
  exists_linearEquiv_regularDifferentials_omegaSpace_zero' hC hRT
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsEquivRegularDifferentials
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
