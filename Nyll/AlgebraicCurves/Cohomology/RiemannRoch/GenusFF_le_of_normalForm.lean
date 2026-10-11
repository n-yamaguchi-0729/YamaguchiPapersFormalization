/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genusFF_le_of_normalForm.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Exists_poleDivisor_of_transcendental
import Nyll.AlgebraicCurves.FunctionFields.Exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
import Nyll.AlgebraicCurves.Divisors.Degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental

/-!
# Genus FF le of normal Form
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusFF_le_of_normalForm
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
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open _root_.AlgebraicCurve
open _root_.Polynomial

universe u v

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace GenusNormalForm
open _root_.AlgebraicCurve

variable {L : Type u} {F' : Type v} [Field L] [Field F'] [Algebra L F']

theorem mem_toValuationSubring_of_adicValuation_le_one (v : Place L F') {f : F'}
    (hf : v.adicValuation f ≤ 1) : f ∈ v.toValuationSubring := by
  by_contra hmem
  have hf0 : f ≠ 0 := fun h => hmem (h ▸ v.toValuationSubring.zero_mem)
  have hinv : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left
    hmem
  have hnu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    apply hmem
    have hwF : (f⁻¹ : F') * (w : F') = 1 := by
      have := congrArg (fun z : v.toValuationSubring => (z : F')) hw
      simpa using this
    have hwf : (w : F') = f := by
      have h2 := congrArg (fun z => f * z) hwF
      simp only [← mul_assoc, mul_inv_cancel₀ hf0, one_mul, mul_one] at h2
      exact h2
    rw [← hwf]
    exact w.2
  have hmax : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring
    :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hlt : v.adicValuation f⁻¹ < 1 := by
    rw [← Place.heightOneSpectrum_asIdeal] at hmax
    have := (v.heightOneSpectrum.valuation_lt_one_iff_mem (K := F') ⟨f⁻¹, hinv⟩).mpr hmax
    simpa [Place.adicValuation] using this
  rw [map_inv₀] at hlt
  have h1 : 1 < v.adicValuation f := by
    have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
    rwa [inv_lt_one₀ (zero_lt_iff.mpr hne)] at hlt
  exact absurd hf (not_le.mpr h1)

theorem mem_toValuationSubring_iff_ord (v : Place L F') {f : F'} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  constructor
  · intro h
    exact ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf
  · intro h
    exact mem_toValuationSubring_of_adicValuation_le_one v ((v.adicValuation_le_one_iff).mpr
      (Or.inr h))

theorem mem_toValuationSubring_of_table (v : Place L F') (t : F') (ht : t ∈ v.toValuationSubring)
    {m : ℕ} (r : Fin (m + 1) → F') (hr0 : r 0 = 1)
    (hmul : ∀ i j, ∃ c : Fin (m + 1) → L[X], r i * r j = ∑ l, Polynomial.aeval t (c l) * r l)
    (i : Fin (m + 1)) : r i ∈ v.toValuationSubring := by
  classical
  let alg : Algebra L[X] F' := (Polynomial.aeval t : L[X] →ₐ[L] F').toRingHom.toAlgebra
  have halg : ∀ f : L[X], algebraMap L[X] F' f = Polynomial.aeval t f := fun _ => rfl
  have hsmul : ∀ (c : L[X]) (f : F'), c • f = Polynomial.aeval t c * f := fun c f =>
    Algebra.smul_def c f
  set M : Submodule L[X] F' := Submodule.span L[X] (Set.range r) with hM
  have hmemM : ∀ f : F', f ∈ M ↔ ∃ c : Fin (m + 1) → L[X], f = ∑ i, Polynomial.aeval t (c i) * r i
    := by
    intro f
    rw [hM, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, by simp [hsmul]⟩
    · rintro ⟨c, rfl⟩; exact ⟨c, by simp [hsmul]⟩
  have hrM : ∀ i, r i ∈ M := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hmulM : ∀ a b : F', a ∈ M → b ∈ M → a * b ∈ M := by
    intro a b ha hb
    obtain ⟨c, rfl⟩ := (hmemM a).mp ha
    obtain ⟨d, rfl⟩ := (hmemM b).mp hb
    rw [Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have : Polynomial.aeval t (c i) * r i * (Polynomial.aeval t (d j) * r j)
        = (c i * d j) • (r i * r j) := by
      rw [hsmul, map_mul]; ring
    rw [this]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c', hc'⟩ := hmul i j
    rw [hc']
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← hsmul]
    exact Submodule.smul_mem _ _ (hrM k)
  have honeM : (1 : F') ∈ M := hr0 ▸ hrM 0
  let S : Subalgebra L[X] F' :=
    { carrier := M
      mul_mem' := fun {a b} ha hb => hmulM a b ha hb
      one_mem' := honeM
      add_mem' := fun {a b} ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      algebraMap_mem' := fun q => by
        have : algebraMap L[X] F' q = q • (1 : F') := by rw [Algebra.smul_def, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ honeM }
  have hfg : (Subalgebra.toSubmodule S).FG := ⟨Finset.univ.image r, by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; rfl⟩
  have hint : IsIntegral L[X] (r i) := IsIntegral.of_mem_of_fg S hfg (r i) (hrM i)
  obtain ⟨P, hPm, hPz⟩ := hint
  let φ : L[X] →+* v.toValuationSubring :=
    (Polynomial.aeval (⟨t, ht⟩ : v.toValuationSubring) : L[X] →ₐ[L] v.toValuationSubring).toRingHom
  have hφ : (algebraMap v.toValuationSubring F').comp φ = algebraMap L[X] F' := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [φ, halg]
    · simp [φ, halg]
  have hint' : IsIntegral v.toValuationSubring (r i) := by
    refine ⟨P.map φ, hPm.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hφ]
    exact hPz
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.toValuationSubring) (K := F')).mp
    hint'
  rw [← hz]
  exact z.2

/-- Reverse the coefficients up to degree `d`, with zero padding when the polynomial has
smaller degree. -/
noncomputable def rev (d : ℕ) (q : L[X]) : L[X] :=
  ∑ n ∈ Finset.range (d + 1), Polynomial.C (q.coeff n) * Polynomial.X ^ (d - n)

theorem pow_mul_aeval_eq_aeval_rev {d : ℕ} {q : L[X]} (hq : q.natDegree ≤ d) {t w : F'}
    (hwt : w * t = 1) : w ^ d * Polynomial.aeval t q = Polynomial.aeval w (rev d q) := by
  have hq' : Polynomial.aeval t q = ∑ n ∈ Finset.range (d + 1), algebraMap L F' (q.coeff n) * t ^
    n := by
    conv_lhs => rw [Polynomial.as_sum_range' q (d + 1) (Nat.lt_succ_of_le hq)]
    simp [Polynomial.aeval_monomial]
  rw [hq', Finset.mul_sum]
  simp only [rev, map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnd : n ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hpow : w ^ d = w ^ (d - n) * w ^ n := by rw [← pow_add, Nat.sub_add_cancel hnd]
  rw [hpow]
  have hwt' : w ^ n * t ^ n = 1 := by rw [← mul_pow, hwt, one_pow]
  calc w ^ (d - n) * w ^ n * ((algebraMap L F') (q.coeff n) * t ^ n)
      = (algebraMap L F') (q.coeff n) * w ^ (d - n) * (w ^ n * t ^ n) := by ring
    _ = (algebraMap L F') (q.coeff n) * w ^ (d - n) := by rw [hwt', mul_one]

theorem ne_zero_of_hind {g : ℕ} (y : F') (s : Fin (g + 1) → F')
    (hind : ∀ d : Fin (g + 1) → L[X], ∑ i, Polynomial.aeval y (d i) * s i = 0 → d = 0)
    (i : Fin (g + 1)) : s i ≠ 0 := by
  classical
  intro h
  have := hind (Pi.single i 1) (by
    rw [Finset.sum_eq_single i]
    · simp [h]
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · intro hi; exact absurd (Finset.mem_univ i) hi)
  have := congrFun this i
  simp at this

end AlgebraicCurve.GenusNormalForm

open AlgebraicCurve.GenusNormalForm in
theorem _root_.AlgebraicCurve.genusFF_le_of_normalForm
    {L : Type u} {F' : Type v} [Field L] [IsAlgClosed L] [Field F'] [Algebra L F']
    (n : ℕ) (y : F') (hy : Transcendental L y)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({y} : Set F')) F')
    (hdegF : Module.finrank (IntermediateField.adjoin L ({y} : Set F')) F' = n + 1)
    (s : Fin (n + 1) → F') (d : Fin (n + 1) → ℕ) (hs0 : s 0 = 1) (hd0 : d 0 = 0)
    (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (c : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → L[X])
    (hmul : ∀ i j, s i * s j = ∑ k, Polynomial.aeval y (c i j k) * s k)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → (c i j k).natDegree ≤ d i + d j - d k)
    (hind : ∀ e : Fin (n + 1) → L[X], ∑ i, Polynomial.aeval y (e i) * s i = 0 → e = 0) :
    genusFF L F' + n ≤ ∑ i, d i := by
  classical
  have := hfd
  have hdle : ∀ i, d i ≤ 2 := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hd0]; exact Nat.zero_le _
    · rcases hd i hi with h | h <;> omega
  have hdsum : ∀ i j k, i ≠ 0 → j ≠ 0 → d k ≤ d i + d j := by
    intro i j k hi hj
    have := hdle k
    rcases hd i hi with h1 | h1 <;> rcases hd j hj with h2 | h2 <;> omega
  obtain ⟨D, hD⟩ := AlgebraicCurve.exists_poleDivisor_of_transcendental y hy
  obtain ⟨-, M, hM1, hM⟩ := AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental y
    hy D hD
  have hdegD : Divisor.degree D = (n + 1 : ℕ) := by
    rw [AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental y hy
      D hD, hdegF]
  have hDnn : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact le_max_left _ _
  have hy0 : y ≠ 0 := by
    intro h
    exact hy (h ▸ isAlgebraic_zero)
  have hs0' : ∀ i, s i ≠ 0 := ne_zero_of_hind y s hind
  set w : F' := y⁻¹ with hw
  have hwy : w * y = 1 := inv_mul_cancel₀ hy0
  have hfin : ∀ v : Place L F', y ∈ v.toValuationSubring → ∀ i, s i ∈ v.toValuationSubring := by
    intro v hyv i
    exact mem_toValuationSubring_of_table v y hyv s hs0 (fun i j => ⟨c i j, hmul i j⟩) i
  let r : Fin (n + 1) → F' := fun i => w ^ (d i) * s i
  have hr0 : r 0 = 1 := by simp [r, hd0, hs0]
  have hrmul : ∀ i j, ∃ c' : Fin (n + 1) → L[X], r i * r j = ∑ l, Polynomial.aeval w (c' l) * r l
    := by
    intro i j
    by_cases hi : i = 0
    · refine ⟨Pi.single j 1, ?_⟩
      subst hi
      rw [hr0, one_mul, Finset.sum_eq_single j]
      · simp
      · intro l _ hl; simp [Pi.single_eq_of_ne hl]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    by_cases hj : j = 0
    · refine ⟨Pi.single i 1, ?_⟩
      subst hj
      rw [hr0, mul_one, Finset.sum_eq_single i]
      · simp
      · intro l _ hl; simp [Pi.single_eq_of_ne hl]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    refine ⟨fun k => rev (d i + d j - d k) (c i j k), ?_⟩
    have hexp : r i * r j = w ^ (d i + d j) * (s i * s j) := by
      simp only [r]; rw [pow_add]; ring
    rw [hexp, hmul i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsplit : w ^ (d i + d j) = w ^ (d i + d j - d k) * w ^ (d k) := by
      rw [← pow_add, Nat.sub_add_cancel (hdsum i j k hi hj)]
    rw [hsplit]
    have : w ^ (d i + d j - d k) * w ^ d k * (Polynomial.aeval y (c i j k) * s k)
        = (w ^ (d i + d j - d k) * Polynomial.aeval y (c i j k)) * (w ^ d k * s k) := by ring
    rw [this, pow_mul_aeval_eq_aeval_rev (hdeg i j k hi hj) hwy]
  have hpole : ∀ v : Place L F', y ∉ v.toValuationSubring → ∀ i,
      w ^ (d i) * s i ∈ v.toValuationSubring := by
    intro v hyv i
    have hwv : w ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem y).resolve_left hyv
    exact mem_toValuationSubring_of_table v w hwv r hr0 hrmul i
  set N : ℕ := M + 2 with hN
  have hMN : M ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  let fam : (Σ i : Fin (n + 1), Fin (N + 1 - d i)) → F' := fun ι => y ^ (ι.2 : ℕ) * s ι.1
  have hmem : ∀ ι, fam ι ∈ LSpace (N • D) := by
    rintro ⟨i, j⟩
    have hjN : (j : ℕ) + d i ≤ N := by have := j.2; have := hdle i; omega
    rw [mem_lSpace_iff_ord]
    right
    intro v
    have hNDv : (N • D) v = (N : ℤ) * D v := by simp
    rw [hNDv]
    change -((N : ℤ) * D v) ≤ v.ord (y ^ (j : ℕ) * s i)
    by_cases hyv : y ∈ v.toValuationSubring
    · have hyord : 0 ≤ v.ord y := (mem_toValuationSubring_iff_ord v hy0).mp hyv
      have h0 : -((N : ℤ) * D v) ≤ 0 := by have := hDnn v; nlinarith
      refine h0.trans ?_
      rw [v.ord_mul (pow_ne_zero _ hy0) (hs0' _), ← zpow_natCast, v.ord_zpow]
      have := (mem_toValuationSubring_iff_ord v (hs0' i)).mp (hfin v hyv i)
      positivity
    · have hyord : v.ord y < 0 := by
        by_contra h
        exact hyv ((mem_toValuationSubring_iff_ord v hy0).mpr (not_lt.mp h))
      have hDv : D v = -v.ord y := by rw [hD v]; exact max_eq_right (by omega)
      have hws : w ^ (d i) * s i ≠ 0 := mul_ne_zero (pow_ne_zero _ (inv_ne_zero hy0)) (hs0' _)
      have hsplit : y ^ (j : ℕ) * s i = y ^ ((j : ℕ) + d i) * (w ^ (d i) * s i) := by
        rw [pow_add]
        have : y ^ (d i) * w ^ (d i) = 1 := by rw [← mul_pow, mul_comm, hwy, one_pow]
        calc
          y ^ (j : ℕ) * s i = y ^ (j : ℕ) * (y ^ (d i) * w ^ (d i)) * s i := by
            rw [this, mul_one]
          _ = _ := by ring
      rw [hsplit, v.ord_mul (pow_ne_zero _ hy0) hws, ← zpow_natCast, v.ord_zpow, hDv]
      have hint := (mem_toValuationSubring_iff_ord v hws).mp (hpole v hyv i)
      have hj : (((j : ℕ) + d i : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hjN
      push_cast at hj ⊢
      nlinarith
  have hli : LinearIndependent L fam := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    let e : Fin (n + 1) → L[X] := fun i =>
      ∑ j : Fin (N + 1 - d i), Polynomial.monomial (j : ℕ) (a ⟨i, j⟩)
    have hsum : ∑ i, Polynomial.aeval y (e i) * s i = 0 := by
      simp only [e, map_sum, Polynomial.aeval_monomial, Finset.sum_mul]
      rw [← ha, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [fam, Algebra.smul_def, mul_assoc]
    have he := hind e hsum
    rintro ⟨i, j⟩
    have := congrArg (fun q : L[X] => q.coeff (j : ℕ)) (congrFun he i)
    simp only [e, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Pi.zero_apply,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      rw [ite_eq_right]
      exact fun h => hb (Fin.ext h)
    · intro h; exact absurd (Finset.mem_univ j) h
  have hRN := hM N hMN
  have hRN1 := hM (N + 1) (by omega)
  have : Module.Finite L (LSpace (N • D)) := by
    by_contra hnf
    have h0 : ell (N • D) = 0 := Module.finrank_of_not_finite hnf
    have hnf' : ¬Module.Finite L (LSpace ((N + 1) • D)) := by
      intro hf
      apply hnf
      have hle : LSpace (N • D) ≤ LSpace ((N + 1) • D) :=
        lSpace_mono (by
          intro v
          simp only [Finsupp.coe_smul, Pi.smul_apply]
          exact nsmul_le_nsmul_left (hDnn v) (Nat.le_succ N))
      exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    have h1 : ell ((N + 1) • D) = 0 := Module.finrank_of_not_finite hnf'
    rw [h0] at hRN
    rw [h1] at hRN1
    rw [hdegD] at hRN hRN1
    push_cast at hRN hRN1
    nlinarith
  let famL : (Σ i : Fin (n + 1), Fin (N + 1 - d i)) → LSpace (N • D) := fun ι => ⟨fam ι, hmem ι⟩
  have hliL : LinearIndependent L famL := by
    apply LinearIndependent.of_comp (LSpace (N • D)).subtype
    exact hli
  have hcard := hliL.fintype_card_le_finrank
  simp only [Fintype.card_sigma, Fintype.card_fin] at hcard
  have hcardZ : (∑ i : Fin (n + 1), ((N : ℤ) + 1 - d i)) ≤ (ell (N • D) : ℤ) := by
    have : ((∑ i : Fin (n + 1), (N + 1 - d i) : ℕ) : ℤ) = ∑ i : Fin (n + 1), ((N : ℤ) + 1 - d i)
      := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hdle i
      omega
    rw [← this]
    exact_mod_cast hcard
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at hcardZ
  rw [hdegD] at hRN
  push_cast at hcardZ hRN
  have : (genusFF L F' : ℤ) + n ≤ ∑ i, (d i : ℤ) := by nlinarith
  exact_mod_cast this
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusFF_le_of_normalForm
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
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
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
