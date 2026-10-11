/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_sum_traceAlong_of_separableAlong_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.Differentials.Polar
import AlgebraicCurves.Differentials.Residues.FibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates
import AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental_of_perfectField
import AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver

/-!
# Place is Regular At and has Simple Pole At and has Simple Residue sum trace Along of
separable Along of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.SimpleResidueTraceSum
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open _root_.AlgebraicCurve.RationalFunctionField in
attribute [-instance]
  instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

noncomputable section

open KaehlerDifferential IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace ResTraceAlgClosedProof
open _root_.AlgebraicCurve

section Rational

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem algebraMap_residueField_bijective [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    Function.Bijective (algebraMap K v.ResidueField) := by
  have : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem trace_residueField_algebraMap [IsAlgClosed K] [IsCurveOver K F] (v : Place K F)
    (r : K) : Algebra.trace K v.ResidueField (algebraMap K v.ResidueField r) = r := by
  have hb := algebraMap_residueField_bijective v
  let e : K ≃ₗ[K] v.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap K v.ResidueField) hb
  have hfin : Module.finrank K v.ResidueField = 1 := by
    rw [← e.finrank_eq, Module.finrank_self]
  rw [Algebra.trace_algebraMap, hfin, one_smul]

theorem trace_residueField_eq_zero_iff [IsAlgClosed K] [IsCurveOver K F] (v : Place K F)
    (z : v.ResidueField) : Algebra.trace K v.ResidueField z = 0 ↔ z = 0 := by
  obtain ⟨r, rfl⟩ := (algebraMap_residueField_bijective v).2 z
  rw [trace_residueField_algebraMap, map_eq_zero_iff _ (algebraMap K v.ResidueField).injective]

theorem eq_algebraMap_of_trace_eq [IsAlgClosed K] [IsCurveOver K F] (v : Place K F)
    {z : v.ResidueField} {s : K} (h : Algebra.trace K v.ResidueField z = s) :
    z = algebraMap K v.ResidueField s := by
  obtain ⟨r, rfl⟩ := (algebraMap_residueField_bijective v).2 z
  rw [trace_residueField_algebraMap] at h
  rw [h]

end Rational

section DVR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_pow_mul_not_mem (v : Place K F) {T : F} (hT : T ∉ v.toValuationSubring) :
    ∃ k : ℕ, v.uniformizer ^ k * T ∉ v.toValuationSubring ∧
      v.uniformizer ^ (k + 1) * T ∈ v.toValuationSubring := by
  set A := v.toValuationSubring with hA
  have hT0 : T ≠ 0 := fun h => hT (h ▸ A.zero_mem)
  have hTi : T⁻¹ ∈ A := (A.mem_or_inv_mem T).resolve_left hT
  set y : A := ⟨T⁻¹, hTi⟩ with hy
  have hy0 : y ≠ 0 := by
    intro h
    have h' : (T⁻¹ : F) = 0 := by
      have := congrArg Subtype.val h
      simpa [hy] using this
    exact hT0 (inv_eq_zero.mp h')
  have hyu : ¬ IsUnit y := by
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hbF : T⁻¹ * (b : F) = 1 := by
      have := congrArg Subtype.val hb
      simpa [hy] using this
    have hbT : (b : F) = T := by
      calc (b : F) = T * (T⁻¹ * (b : F)) := by rw [← mul_assoc, mul_inv_cancel₀ hT0, one_mul]
        _ = T := by rw [hbF, mul_one]
    exact hT (hbT ▸ b.2)
  set ϖ : A := ⟨v.uniformizer, v.uniformizer_mem_toValuationSubring⟩ with hϖdef
  have hϖ : Irreducible ϖ := v.irreducible_mk_uniformizer
  obtain ⟨n, u, hyu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    apply hyu
    rw [hyu', pow_zero, mul_one]
    exact u.isUnit
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨k, ?_, ?_⟩
  · intro hmem
    have hπ0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
    have hU0 : ((u : A) : F) ≠ 0 := by
      intro h0
      apply u.ne_zero
      exact Subtype.ext h0
    have hF : T⁻¹ = ((u : A) : F) * v.uniformizer ^ (k + 1) := by
      have := congrArg Subtype.val hyu'
      simpa [hy, hϖdef] using this
    have hinv : v.uniformizer⁻¹ = ((u : A) : F) * (v.uniformizer ^ k * T) := by
      have h1 : ((u : A) : F) * (v.uniformizer ^ k * T) * v.uniformizer = 1 := by
        calc ((u : A) : F) * (v.uniformizer ^ k * T) * v.uniformizer
            = (((u : A) : F) * v.uniformizer ^ (k + 1)) * T := by ring
          _ = T⁻¹ * T := by rw [← hF]
          _ = 1 := inv_mul_cancel₀ hT0
      exact (eq_inv_of_mul_eq_one_left h1).symm
    have hinvmem : v.uniformizer⁻¹ ∈ A := by
      rw [hinv]
      exact mul_mem (u : A).2 hmem
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨⟨v.uniformizer⁻¹, hinvmem⟩, ?_⟩
    apply Subtype.ext
    simp [hϖdef, mul_inv_cancel₀ hπ0]
  · have hF : T⁻¹ = ((u : A) : F) * v.uniformizer ^ (k + 1) := by
      have := congrArg Subtype.val hyu'
      simpa [hy, hϖdef] using this
    have hU0 : ((u : A) : F) ≠ 0 := by
      intro h0
      apply u.ne_zero
      exact Subtype.ext h0
    have hval : v.uniformizer ^ (k + 1) * T = (((u⁻¹ : Aˣ) : A) : F) := by
      have hUinv : (((u⁻¹ : Aˣ) : A) : F) = (((u : A) : F))⁻¹ := by
        have h1 : ((u : A) : F) * (((u⁻¹ : Aˣ) : A) : F) = 1 := by
          rw [← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            OneMemClass.coe_one]
        exact (eq_inv_of_mul_eq_one_right h1)
      rw [hUinv]
      have h2 : ((u : A) : F) * (v.uniformizer ^ (k + 1) * T) = 1 := by
        calc ((u : A) : F) * (v.uniformizer ^ (k + 1) * T)
            = (((u : A) : F) * v.uniformizer ^ (k + 1)) * T := by ring
          _ = T⁻¹ * T := by rw [← hF]
          _ = 1 := inv_mul_cancel₀ hT0
      exact (eq_inv_of_mul_eq_one_right h2)
    rw [hval]
    exact SetLike.coe_mem _

theorem residue_ne_zero_of_not_mem (v : Place K F) {y : F} (hy : y ∉ v.toValuationSubring)
    (hπy : v.uniformizer * y ∈ v.toValuationSubring) :
    residue v.toValuationSubring ⟨v.uniformizer * y, hπy⟩ ≠ 0 := by
  intro h0
  rw [residue_eq_zero_iff, v.irreducible_mk_uniformizer.maximalIdeal_eq,
    Ideal.mem_span_singleton'] at h0
  obtain ⟨z, hz⟩ := h0
  have hzF : (z : F) * v.uniformizer = v.uniformizer * y := by
    have := congrArg Subtype.val hz
    simpa using this
  have hyz : y = (z : F) := by
    have hπ0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
    have : v.uniformizer * y = v.uniformizer * (z : F) := by rw [← hzF, mul_comm]
    exact mul_left_cancel₀ hπ0 this
  exact hy (hyz ▸ z.2)

theorem exists_eq_uniformizer_mul_of_not_isUnit (w : Place K F) {a : F}
    (ha : a ∈ w.toValuationSubring) (hu : ¬ IsUnit (⟨a, ha⟩ : w.toValuationSubring)) :
    ∃ b ∈ w.toValuationSubring, a = w.uniformizer * b := by
  have hmem : (⟨a, ha⟩ : w.toValuationSubring) ∈ maximalIdeal w.toValuationSubring :=
    (mem_maximalIdeal _).mpr hu
  rw [w.irreducible_mk_uniformizer.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  simp only [MulMemClass.coe_mul] at this
  rw [← this, mul_comm]

end DVR

section Main

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem main [IsAlgClosed K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    {x' : F'} (htr' : Transcendental K x')
    (hfd' : FiniteDimensional ↥(IntermediateField.adjoin K ({x'} : Set F')) F')
    [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hsep : SeparableAlong K φ)
    (v : Place K F) (η : Ω[F'⁄K]) :
    ((∀ w ∈ Place.fiberAlong φ hφ v, w.IsRegularAt η) →
        v.IsRegularAt (Differential.traceAlong φ η)) ∧
    ((∀ w ∈ Place.fiberAlong φ hφ v, w.HasSimplePoleAt η) →
        v.HasSimplePoleAt (Differential.traceAlong φ η)) ∧
    (∀ r : Place K F' → K,
      (∀ w ∈ Place.fiberAlong φ hφ v, w.HasSimpleResidue η (r w)) →
        v.HasSimpleResidue (Differential.traceAlong φ η)
          (∑ w ∈ Place.fiberAlong φ hφ v, r w)) := by
  classical
  have hcF : IsCurveOver K F := isCurveOver_of_transcendental_of_perfectField htr hfd
  have hcF' : IsCurveOver K F' := isCurveOver_of_transcendental_of_perfectField htr' hfd'
  have : Algebra.EssFiniteType K F := essFiniteType_of_transcendental_of_finiteDimensional htr hfd
  have : Algebra.EssFiniteType K F' :=
    essFiniteType_of_transcendental_of_finiteDimensional htr' hfd'
  have hgF : ∀ u : Place K F, u.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hgF' : ∀ w : Place K F', w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hrkF : Module.finrank F Ω[F⁄K] = 1 := hcF.kaehler_free_rank_one.2
  have hrkF' : Module.finrank F' Ω[F'⁄K] = 1 := hcF'.kaehler_free_rank_one.2
  have : Nontrivial Ω[F⁄K] := Module.nontrivial_of_finrank_eq_succ (n := 0) hrkF
  have : Nontrivial Ω[F'⁄K] := Module.nontrivial_of_finrank_eq_succ (n := 0) hrkF'
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : Algebra.IsSeparable F F' := hsep
  have : Algebra.EssFiniteType F F' := Algebra.EssFiniteType.of_comp K F F'
  have hfinI : Module.Finite F F' := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hfin : FiniteAlong K φ := hfinI
  have hfib : FibreResidueIdentityAlong φ hφ :=
    fibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates φ hφ hfin hsep
  set ω' : Ω[F'⁄K] := Differential.pullbackAlong φ v.dCoord with hω'
  have hω0 : v.dCoord ≠ 0 := v.dCoord_ne_zero
  have hω'ne : ω' ≠ 0 := by
    obtain ⟨u, hu⟩ : ∃ u : F', Algebra.trace F F' u ≠ 0 := by
      by_contra hall
      apply Algebra.trace_ne_zero F F'
      ext u
      by_contra hu
      exact hall ⟨u, hu⟩
    intro h0
    have h1 := Differential.traceAlong_smul_pullbackAlong φ hsep u v.dCoord
    rw [← hω', h0, smul_zero, map_zero] at h1
    exact smul_ne_zero hu hω0 h1.symm
  obtain ⟨g, hg⟩ : ∃ g : F', g • ω' = η := (finrank_eq_one_iff_of_nonzero' ω' hω'ne).mp hrkF' η
  set T : F := Algebra.trace F F' g with hT
  have htrace : Differential.traceAlong φ η = T • v.dCoord := by
    rw [← hg, hω', Differential.traceAlong_smul_pullbackAlong φ hsep]
  set c : Place K F' → F' := fun w => w.differentialCoeff ω' with hc
  have hηw : ∀ w : Place K F', η = (g * c w) • w.dCoord := by
    intro w
    rw [← hg, mul_smul, hc]
    simp only
    rw [w.differentialCoeff_smul_dCoord ω']
  have huniq : ∀ (w : Place K F') (f : F'), η = f • w.dCoord → f = g * c w :=
    fun w f hf => (w.differentialCoeff_unique hf).symm.trans (w.differentialCoeff_unique (hηw w))
  have hmemφ : ∀ w ∈ Place.fiberAlong φ hφ v, ∀ a : F,
      a ∈ v.toValuationSubring ↔ φ a ∈ w.toValuationSubring := by
    intro w hw a
    have hwv : w.restrictAlong φ hφ = v := Place.mem_fiberAlong.mp hw
    rw [← hwv]
    exact Iff.rfl
  have hφπ : ∀ w ∈ Place.fiberAlong φ hφ v,
      ∃ b ∈ w.toValuationSubring, φ v.uniformizer = w.uniformizer * b := by
    intro w hw
    have hmem : φ v.uniformizer ∈ w.toValuationSubring :=
      (hmemφ w hw _).mp v.uniformizer_mem_toValuationSubring
    refine exists_eq_uniformizer_mul_of_not_isUnit w hmem ?_
    intro hunit
    obtain ⟨b, hb⟩ := hunit.exists_right_inv
    have hbF : φ v.uniformizer * (b : F') = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have hπ0 : φ v.uniformizer ≠ 0 := by
      rw [map_ne_zero_iff φ φ.toRingHom.injective]
      exact v.uniformizer_ne_zero
    have hbinv : (b : F') = φ (v.uniformizer⁻¹) := by
      rw [map_inv₀]
      exact (eq_inv_of_mul_eq_one_right hbF)
    have hinvmem : v.uniformizer⁻¹ ∈ v.toValuationSubring := by
      rw [hmemφ w hw, ← hbinv]
      exact b.2
    apply v.irreducible_mk_uniformizer.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨⟨v.uniformizer⁻¹, hinvmem⟩, ?_⟩
    apply Subtype.ext
    simp [mul_inv_cancel₀ v.uniformizer_ne_zero]
  have hprobe : ∀ a : F,
      ∑ w ∈ Place.fiberAlong φ hφ v,
          Algebra.trace K w.ResidueField (w.localResidue (φ a * g * c w))
        = Algebra.trace K v.ResidueField (v.localResidue (a * T)) := by
    intro a
    have h := hfib v v.dCoord (φ a * g)
    simp only [kaehlerResidueTerm, diagonalHom_apply, traceFunAlong_apply] at h
    rw [v.differentialCoeff_dCoord, mul_one] at h
    have htr' : Algebra.trace F F' (φ a * g) = a * T := by
      have hsm : φ a * g = a • g := (Algebra.smul_def a g).symm
      rw [hsm, LinearMap.map_smul, smul_eq_mul]
    rw [htr'] at h
    convert h using 1
  have hterm0 : ∀ (w : Place K F') (z : F'), z ∈ w.toValuationSubring →
      Algebra.trace K w.ResidueField (w.localResidue z) = 0 := by
    intro w z hz
    rw [w.localResidue_of_mem hz, map_zero]
  have hRHS : ∀ y : F, y ∉ v.toValuationSubring → v.uniformizer * y ∈ v.toValuationSubring →
      Algebra.trace K v.ResidueField (v.localResidue y) ≠ 0 := by
    intro y hy hπy
    rw [Ne, trace_residueField_eq_zero_iff, v.localResidue_simplePole y hπy]
    exact residue_ne_zero_of_not_mem v hy hπy
  have hpole_engine : (∀ w ∈ Place.fiberAlong φ hφ v,
      w.uniformizer * (g * c w) ∈ w.toValuationSubring) →
      v.uniformizer * T ∈ v.toValuationSubring := by
    intro hsp
    by_contra hnot
    obtain ⟨k, hk1, hk2⟩ := exists_pow_mul_not_mem v hnot
    have hL : ∑ w ∈ Place.fiberAlong φ hφ v,
        Algebra.trace K w.ResidueField
          (w.localResidue (φ (v.uniformizer ^ (k + 1)) * g * c w)) = 0 := by
      refine Finset.sum_eq_zero fun w hw => hterm0 w _ ?_
      obtain ⟨b, hb, hbeq⟩ := hφπ w hw
      have hφπmem : φ v.uniformizer ∈ w.toValuationSubring :=
        (hmemφ w hw _).mp v.uniformizer_mem_toValuationSubring
      have hrew : φ (v.uniformizer ^ (k + 1)) * g * c w
          = (φ v.uniformizer) ^ k * (b * (w.uniformizer * (g * c w))) := by
        rw [map_pow, pow_succ]
        rw [show φ v.uniformizer ^ k * φ v.uniformizer * g * c w
            = φ v.uniformizer ^ k * (φ v.uniformizer * (g * c w)) by ring, hbeq]
        ring
      rw [hrew]
      exact mul_mem (pow_mem hφπmem k) (mul_mem hb (hsp w hw))
    have hk2' : v.uniformizer * (v.uniformizer ^ k * (v.uniformizer * T))
        ∈ v.toValuationSubring := by
      rw [show v.uniformizer * (v.uniformizer ^ k * (v.uniformizer * T))
          = v.uniformizer ^ (k + 1) * (v.uniformizer * T) by ring]
      exact hk2
    have hR := hRHS (v.uniformizer ^ k * (v.uniformizer * T)) hk1 hk2'
    have hp := hprobe (v.uniformizer ^ (k + 1))
    rw [hL] at hp
    apply hR
    rw [show v.uniformizer ^ k * (v.uniformizer * T) = v.uniformizer ^ (k + 1) * T by ring]
    exact hp.symm
  refine ⟨fun hreg => ?_, fun hpole => ?_, fun r hres => ?_⟩
  · have hint : ∀ w ∈ Place.fiberAlong φ hφ v, g * c w ∈ w.toValuationSubring := by
      intro w hw
      obtain ⟨f, hf, hfeq⟩ := hreg w hw
      rw [← huniq w f hfeq]
      exact hf
    have hTmem : T ∈ v.toValuationSubring := by
      by_contra hnot
      obtain ⟨k, hk1, hk2⟩ := exists_pow_mul_not_mem v hnot
      have hL : ∑ w ∈ Place.fiberAlong φ hφ v,
          Algebra.trace K w.ResidueField
            (w.localResidue (φ (v.uniformizer ^ k) * g * c w)) = 0 := by
        refine Finset.sum_eq_zero fun w hw => hterm0 w _ ?_
        have hφπmem : φ v.uniformizer ∈ w.toValuationSubring :=
          (hmemφ w hw _).mp v.uniformizer_mem_toValuationSubring
        rw [map_pow, mul_assoc]
        exact mul_mem (pow_mem hφπmem k) (hint w hw)
      have hk2' : v.uniformizer * (v.uniformizer ^ k * T) ∈ v.toValuationSubring := by
        rw [show v.uniformizer * (v.uniformizer ^ k * T) = v.uniformizer ^ (k + 1) * T by ring]
        exact hk2
      have hR := hRHS (v.uniformizer ^ k * T) hk1 hk2'
      have hp := hprobe (v.uniformizer ^ k)
      rw [hL] at hp
      exact hR hp.symm
    exact ⟨T, hTmem, htrace⟩
  · have hsp : ∀ w ∈ Place.fiberAlong φ hφ v,
        w.uniformizer * (g * c w) ∈ w.toValuationSubring := by
      intro w hw
      obtain ⟨f, hf, hfeq⟩ := hpole w hw
      rw [← huniq w f hfeq]
      exact hf
    exact ⟨T, hpole_engine hsp, htrace⟩
  · have hval : ∀ w ∈ Place.fiberAlong φ hφ v,
        w.HasValue (w.uniformizer * (g * c w)) (r w) := by
      intro w hw
      obtain ⟨f, hfeq, hf⟩ := hres w hw
      rw [← huniq w f hfeq]
      exact hf
    have hπT : v.uniformizer * T ∈ v.toValuationSubring :=
      hpole_engine fun w hw => (hval w hw).mem
    have hp := hprobe 1
    simp only [map_one, one_mul] at hp
    have hL : ∑ w ∈ Place.fiberAlong φ hφ v,
        Algebra.trace K w.ResidueField (w.localResidue (g * c w))
          = ∑ w ∈ Place.fiberAlong φ hφ v, r w := by
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [w.localResidue_simplePole _ (hval w hw).mem, (hval w hw).residue_eq,
        trace_residueField_algebraMap]
    rw [hL] at hp
    have hres_v : residue v.toValuationSubring ⟨v.uniformizer * T, hπT⟩
        = algebraMap K v.ResidueField (∑ w ∈ Place.fiberAlong φ hφ v, r w) := by
      apply eq_algebraMap_of_trace_eq v
      rw [← v.localResidue_simplePole T hπT]
      exact hp.symm
    exact ⟨T, htrace, hπT, hres_v⟩

end Main

end AlgebraicCurve.ResTraceAlgClosedProof

end

open _root_.AlgebraicCurve
end AlgebraicCurves.Places.Proofs.SimpleResidueTraceSum

namespace AlgebraicCurve.Place

open _root_.AlgebraicCurves.Places.Proofs.SimpleResidueTraceSum
  _root_.AlgebraicCurves.Places.Proofs.SimpleResidueTraceSum.AlgebraicCurve in
theorem
isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_sum_traceAlong_of_separableAlong_of_isAlgClosed
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [IsAlgClosed K]
    {x : F} (htr : Transcendental K x) (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({x} :
      Set F)) F)
    {x' : F'} (htr' : Transcendental K x') (hfd' : FiniteDimensional ↥(IntermediateField.adjoin K
      ({x'} : Set F')) F')
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hsep : AlgebraicCurve.SeparableAlong K φ)
    (v : AlgebraicCurve.Place K F) (η : Ω[F'⁄K]) :
    ((∀ w ∈ AlgebraicCurve.Place.fiberAlong φ hφ v, w.IsRegularAt η) →
        v.IsRegularAt (AlgebraicCurve.Differential.traceAlong φ η)) ∧
    ((∀ w ∈ AlgebraicCurve.Place.fiberAlong φ hφ v, w.HasSimplePoleAt η) →
        v.HasSimplePoleAt (AlgebraicCurve.Differential.traceAlong φ η)) ∧
    (∀ r : AlgebraicCurve.Place K F' → K,
      (∀ w ∈ AlgebraicCurve.Place.fiberAlong φ hφ v, w.HasSimpleResidue η (r w)) →
        v.HasSimpleResidue (AlgebraicCurve.Differential.traceAlong φ η)
          (∑ w ∈ AlgebraicCurve.Place.fiberAlong φ hφ v, r w)) :=
  AlgebraicCurve.ResTraceAlgClosedProof.main htr hfd htr' hfd' φ hφ hsep v η
end AlgebraicCurve.Place
end ProofImplementation

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
open ModularCurve.KwNo6Pin in
attribute [-instance]
  isLocalRing_completion
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
open ModularCurve.KwF4gRRTate in
attribute [-instance]
  instAlgebraKAdicCompletionIntegers
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
open IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open _root_.AlgebraicCurve.RationalFunctionField in
attribute [-instance]
  instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicCurve.cechH1.traceAlong_mk
  AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply
  AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk
  AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
attribute [-simp] AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
