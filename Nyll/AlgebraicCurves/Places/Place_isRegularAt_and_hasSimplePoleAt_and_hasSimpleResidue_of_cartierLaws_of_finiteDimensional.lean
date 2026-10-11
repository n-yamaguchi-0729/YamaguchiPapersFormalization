/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Polar
import Nyll.AlgebraicCurves.Places.ExistsUnique_pDigits_of_D_ne_zero
import Mathlib.Data.Nat.Prime.Factorial
import Nyll.AlgebraicCurves.Places.Place_kaehlerD_ne_zero_of_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_ord_nonneg_of_D_eq_smul_D_of_ord_eq_one

/-!
# Place is Regular At and has Simple Pole At and has Simple Residue of cartier Laws of
finite Dimensional
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.SimpleResidueCartier
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open _root_.AlgebraicCurve in
attribute [-instance]
  instFundamentalIdentityOfSumRamificationInertia
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open KaehlerDifferential AlgebraicCurve

namespace CartierLocalPen12

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f :=
  by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {f : F} (hf : f ≠ 0) (hmem : f ∈
  v.toValuationSubring)
    (hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) : 0
      < v.ord f := by
  have h0 : 0 ≤ v.ord f := ord_nonneg_of_mem v hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
    rw [← h, zpow_zero, mul_one] at hu
    have : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this] at hmax
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax u.isUnit

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) (hmem : f ∈
  v.toValuationSubring) :
    (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  change v.ord f = 0 at this
  omega

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  let u : v.toValuationSubringˣ :=
    ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  exact v.ord_coe_unit u

theorem coeff_unique {t : F} (hDt : D K F t ≠ 0) {g g' : F} (h : g • D K F t = g' • D K F t) : g =
  g' := by
  have h' : (g - g') • D K F t = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h' with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hDt

theorem exists_coeff [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (ω : Ω[F⁄K]) : ∃ c : F, ω = c •
  D K F t := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (D K F t) hDt).mp IsCurveOver.finrank_kaehler ω
  exact ⟨c, hc.symm⟩

/-- The coefficient of `D h` relative to the nonzero differential `D t`. -/
noncomputable def deriv [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (h : F) : F :=
  (exists_coeff hDt (D K F h)).choose

theorem D_eq_deriv_smul [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (h : F) :
    D K F h = deriv hDt h • D K F t :=
  (exists_coeff hDt (D K F h)).choose_spec

theorem deriv_eq_of_D_eq [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) {h g : F} (hg : D K F h = g
  • D K F t) :
    deriv hDt h = g :=
  coeff_unique hDt ((D_eq_deriv_smul hDt h).symm.trans hg)

theorem deriv_add [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (h h' : F) :
    deriv hDt (h + h') = deriv hDt h + deriv hDt h' :=
  deriv_eq_of_D_eq hDt (by rw [map_add, D_eq_deriv_smul hDt h, D_eq_deriv_smul hDt h', add_smul])

theorem deriv_zero [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) : deriv hDt (0 : F) = 0 :=
  deriv_eq_of_D_eq hDt (by rw [map_zero, zero_smul])

theorem deriv_sum [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) {ι : Type*} (s : Finset ι) (f : ι →
  F) :
    deriv hDt (∑ i ∈ s, f i) = ∑ i ∈ s, deriv hDt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, deriv_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, deriv_add, ih]

theorem deriv_pow_char_mul [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP F p] {t : F} (hDt : D K
  F t ≠ 0)
    (a h : F) : deriv hDt (a ^ p * h) = a ^ p * deriv hDt h := by
  apply deriv_eq_of_D_eq hDt
  have hDap : D K F (a ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F p, CharP.cast_eq_zero F p, zero_smul]
  rw [Derivation.leibniz, hDap, smul_zero, add_zero, D_eq_deriv_smul hDt h, smul_smul]

theorem deriv_natCast_mul [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP F p] {t : F} (hDt : D K F
  t ≠ 0)
    (m : ℕ) (h : F) : deriv hDt ((m : F) * h) = m * deriv hDt h := by
  have hm : ((m : F)) ^ p = m := by rw [← frobenius_def, map_natCast]
  rw [← hm, deriv_pow_char_mul p hDt, hm]

theorem deriv_t_pow [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (n : ℕ) :
    deriv hDt (t ^ n) = n * t ^ (n - 1) := by
  apply deriv_eq_of_D_eq hDt
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F n, smul_smul]

theorem deriv_iterate_pow_char_mul_t_pow [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP F p] {t :
  F} (hDt : D K F t ≠ 0)
    (a : F) (k n : ℕ) :
    (deriv hDt)^[k] (a ^ p * t ^ n) = a ^ p * ((Nat.descFactorial n k : F) * t ^ (n - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, deriv_pow_char_mul p hDt, deriv_natCast_mul p hDt,
      deriv_t_pow hDt, Nat.descFactorial_succ, Nat.sub_sub, Nat.cast_mul]
    ring

theorem iterate_deriv_sum [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (k : ℕ) {ι : Type*} (s :
  Finset ι)
    (f : ι → F) : (deriv hDt)^[k] (∑ i ∈ s, f i) = ∑ i ∈ s, (deriv hDt)^[k] (f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, deriv_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Function.iterate_succ_apply' (deriv hDt)]

theorem ord_iterate_deriv_nonneg [IsCurveOver K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) (hDt : D K F t ≠ 0) (k : ℕ) {h : F}
    (hh : 0 ≤ v.ord h) : 0 ≤ v.ord ((deriv hDt)^[k] h) := by
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact AlgebraicCurve.Place.ord_nonneg_of_D_eq_smul_D_of_ord_eq_one x v ht ih (D_eq_deriv_smul
      hDt _)

theorem cartier_digits (p : ℕ) [hp : Fact p.Prime] [CharP F p] (t : F)
    (C : Ω[F⁄K] →+ Ω[F⁄K]) (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (D K F f) = 0) (hlog : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)
    (a : Fin p → F) :
    C ((∑ i : Fin p, a i ^ p * t ^ (i : ℕ)) • D K F t) =
      a ⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩ • D K F t := by
  rw [Finset.sum_smul, map_sum]
  have hterm : ∀ i : Fin p, C ((a i ^ p * t ^ (i : ℕ)) • D K F t) =
      if (i : ℕ) = p - 1 then a i • D K F t else 0 := by
    intro i
    rw [mul_smul, hsemi]
    split_ifs with hi
    · rw [hi, hlog]
    · have hi1 : ((i : ℕ) + 1 : F) ≠ 0 := by
        intro h0
        have hdvd := (CharP.cast_eq_zero_iff F p ((i : ℕ) + 1)).mp (by exact_mod_cast h0)
        have hlt : (i : ℕ) + 1 < p := by have := i.2; omega
        exact absurd (Nat.le_of_dvd (Nat.succ_pos _) hdvd) (not_le.mpr hlt)
      set e : F := ((i : ℕ) + 1 : F)⁻¹ with he
      have hep : e ^ p = e := by
        rw [he, inv_pow, ← frobenius_def, map_add, map_natCast, map_one]
      have hD : t ^ (i : ℕ) • D K F t = e • D K F (t ^ ((i : ℕ) + 1)) := by
        rw [Derivation.leibniz_pow, Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul F ((i : ℕ) + 1),
          smul_smul,
          Nat.cast_succ, he, inv_mul_cancel₀ hi1, one_smul]
      rw [hD, ← hep, hsemi, hker, smul_zero, smul_zero]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : (Finset.univ.filter fun i : Fin p => (i : ℕ) = p - 1) =
      {⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
  rw [hfilter, Finset.sum_singleton]

theorem locreg [IsCurveOver K F] (p : ℕ) [hp : Fact p.Prime] [CharP K p] [CharP F p] [PerfectField
  K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K]) (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (D K F f) = 0) (hlog : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)
    (v : Place K F) {t : F} (ht : v.ord t = 1) (hDt : D K F t ≠ 0) {g : F} (hg0 : 0 ≤ v.ord g) :
    ∃ g' : F, 0 ≤ v.ord g' ∧ C (g • D K F t) = g' • D K F t := by
  obtain ⟨a, ha, -⟩ := AlgebraicCurve.existsUnique_pDigits_of_D_ne_zero (K := K) p x hDt g
  set ap := a ⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩ with hapdef
  refine ⟨ap, ?_, by rw [ha]; exact cartier_digits p t C hsemi hker hlog a⟩
  by_cases hap : ap = 0
  · rw [hap, v.ord_zero]
  have hiter : (deriv hDt)^[p - 1] g = ap ^ p * ((Nat.factorial (p - 1) : ℕ) : F) := by
    rw [ha, iterate_deriv_sum hDt]
    simp_rw [deriv_iterate_pow_char_mul_t_pow p hDt]
    rw [Finset.sum_eq_single ⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩]
    · rw [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one, hapdef]
    · intro i _ hi
      have hlt : (i : ℕ) < p - 1 := by
        have h1 := i.2
        have h2 : (i : ℕ) ≠ p - 1 := fun h => hi (Fin.ext h)
        omega
      rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hlt]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hord := ord_iterate_deriv_nonneg x v ht hDt (p - 1) hg0
  rw [hiter] at hord
  have hfact : ¬ p ∣ Nat.factorial (p - 1) := by
    rw [Nat.Prime.dvd_factorial hp.out]
    have := hp.out.pos
    omega
  have hfne : ((Nat.factorial (p - 1) : ℕ) : F) ≠ 0 := fun h0 =>
    hfact ((CharP.cast_eq_zero_iff F p _).mp h0)
  have hnat0 : v.ord ((Nat.factorial (p - 1) : ℕ) : F) = 0 := by
    have h : ((Nat.factorial (p - 1) : ℕ) : F) = algebraMap K F ((Nat.factorial (p - 1) : ℕ) : K) :=
      (map_natCast (algebraMap K F) _).symm
    have hK : ((Nat.factorial (p - 1) : ℕ) : K) ≠ 0 := fun h0 => hfact ((CharP.cast_eq_zero_iff K p
      _).mp h0)
    rw [h]
    exact ord_algebraMap v hK
  rw [v.ord_mul (pow_ne_zero p hap) hfne, hnat0, add_zero, ← zpow_natCast, v.ord_zpow] at hord
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  exact nonneg_of_mul_nonneg_right hord hp0

end CartierLocalPen12
end AlgebraicCurves.Places.Proofs.SimpleResidueCartier

namespace AlgebraicCurve.Place

open _root_.AlgebraicCurves.Places.Proofs.SimpleResidueCartier
open _root_.KaehlerDifferential _root_.AlgebraicCurve


theorem isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
    {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hC1 : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hC2 : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hC3 : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    (v.IsRegularAt ω → v.IsRegularAt (C ω)) ∧
      (v.HasSimplePoleAt ω → v.HasSimplePoleAt (C ω)) ∧
      (∀ r : K, v.HasSimpleResidue ω r → ∃ s : K, s ^ p = r ∧ v.HasSimpleResidue (C ω) s) := by
  classical
  have hp : p.Prime := Fact.out
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  set t := v.uniformizer with htdef
  have ht : v.ord t = 1 := v.ord_uniformizer
  have hDt : KaehlerDifferential.D K F t ≠ 0 := AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one
    x v ht
  have hdc : v.dCoord = KaehlerDifferential.D K F t := v.dCoord_eq
  have ht0 : t ≠ 0 := v.uniformizer_ne_zero
  have htmem : t ∈ v.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg v
    (by rw [ht]; exact zero_le_one)
  have halgmem : ∀ a : K, algebraMap K F a ∈ v.toValuationSubring := fun a => v.algebraMap_mem' a
  have hresalg : ∀ a : K, IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F a, halgmem a⟩ =
      algebraMap K v.ResidueField a := fun a => AlgebraicCurve.Place.residue_algebraMap v a
  have hreg : ∀ ω : Ω[F⁄K], v.IsRegularAt ω → v.IsRegularAt (C ω) := by
    rintro ω ⟨f, hf, rfl⟩
    obtain ⟨g', hg', hC⟩ := CartierLocalPen12.locreg p x C hC1 hC2 hC3 v ht hDt
      (CartierLocalPen12.ord_nonneg_of_mem v hf)
    refine ⟨g', CartierLocalPen12.mem_of_ord_nonneg v hg', ?_⟩
    rw [hdc, hC]
  refine ⟨hreg ω, ?_, ?_⟩
  · rintro ⟨f, htf, rfl⟩
    have hreg' : v.IsRegularAt ((t ^ p * f) • v.dCoord) := by
      refine ⟨t ^ p * f, ?_, rfl⟩
      have e : t ^ p * f = t ^ (p - 1) * (t * f) := by
        rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
      rw [e]
      exact mul_mem (pow_mem htmem _) htf
    obtain ⟨g', hg'mem, hg'⟩ := hreg _ hreg'
    have hsemi' : C ((t ^ p * f) • v.dCoord) = t • C (f • v.dCoord) := by rw [mul_smul, hC1]
    refine ⟨t⁻¹ * g', ?_, ?_⟩
    · rw [← mul_assoc, mul_inv_cancel₀ ht0, one_mul]; exact hg'mem
    · have h1 : t • C (f • v.dCoord) = g' • v.dCoord := hsemi'.symm.trans hg'
      have h2 := congrArg (fun ω => t⁻¹ • ω) h1
      simp only [smul_smul, inv_mul_cancel₀ ht0, one_smul] at h2
      exact h2
  · rintro r ⟨f, rfl, hval⟩
    obtain ⟨hmem, hres⟩ := hval
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨s, hs⟩ : ∃ s : K, s ^ p = r := ⟨(frobeniusEquiv K p).symm r, by
      rw [← frobeniusEquiv_def]; exact (frobeniusEquiv K p).apply_symm_apply r⟩
    set u : F := f - algebraMap K F r * t⁻¹ with hu
    have htu : t * u = t * f - algebraMap K F r := by
      rw [hu, mul_sub, mul_comm (algebraMap K F r) t⁻¹, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]
    have htu_mem : t * u ∈ v.toValuationSubring := by rw [htu]; exact sub_mem hmem (halgmem r)
    have hu_int : 0 ≤ v.ord u := by
      by_cases hu0 : u = 0
      · rw [hu0, v.ord_zero]
      have hmax : (⟨t * u, htu_mem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal
        v.toValuationSubring := by
        have hdiff : (⟨t * f, hmem⟩ : v.toValuationSubring) - ⟨algebraMap K F r, halgmem r⟩ ∈
            IsLocalRing.maximalIdeal v.toValuationSubring := by
          rw [← Ideal.Quotient.eq]
          exact hres.trans (hresalg r).symm
        have heq : (⟨t * u, htu_mem⟩ : v.toValuationSubring) = ⟨t * f, hmem⟩ - ⟨algebraMap K F r,
          halgmem r⟩ :=
          Subtype.ext htu
        rw [heq]; exact hdiff
      have hpos := CartierLocalPen12.ord_pos_of_mem_maximalIdeal v (mul_ne_zero ht0 hu0) htu_mem
        hmax
      rw [v.ord_mul ht0 hu0, ht] at hpos
      omega
    obtain ⟨g', hg', hCu⟩ := CartierLocalPen12.locreg p x C hC1 hC2 hC3 v ht hDt hu_int
    have hpol : C ((algebraMap K F r * t⁻¹) • v.dCoord) = (algebraMap K F s * t⁻¹) • v.dCoord := by
      rw [hdc]
      have e1 : algebraMap K F r * t⁻¹ = (algebraMap K F s * t⁻¹) ^ p * t ^ (p - 1) := by
        rw [mul_pow, ← map_pow, hs, mul_assoc]
        congr 1
        rw [inv_pow, ← zpow_natCast t (p - 1), ← zpow_natCast t p, ← zpow_neg, ← zpow_add₀ ht0,
          Nat.cast_sub hp.one_lt.le, Nat.cast_one]
        have : -(p : ℤ) + ((p : ℤ) - 1) = -1 := by ring
        rw [this, zpow_neg, zpow_one]
      rw [e1, mul_smul, hC1, hC3]
    have hsplit : f • v.dCoord = (algebraMap K F r * t⁻¹) • v.dCoord + u • v.dCoord := by
      rw [← add_smul]; congr 1; rw [hu]; ring
    have hC : C (f • v.dCoord) = (algebraMap K F s * t⁻¹ + g') • v.dCoord := by
      rw [hsplit, map_add, hpol, hdc, hCu, add_smul]
    have hg'mem : g' ∈ v.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg v hg'
    have hval' : t * (algebraMap K F s * t⁻¹ + g') = algebraMap K F s + t * g' := by
      rw [mul_add, mul_comm (algebraMap K F s) t⁻¹, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]
    have hmem' : t * (algebraMap K F s * t⁻¹ + g') ∈ v.toValuationSubring := by
      rw [hval']; exact add_mem (halgmem s) (mul_mem htmem hg'mem)
    refine ⟨s, hs, algebraMap K F s * t⁻¹ + g', hC, hmem', ?_⟩
    have htg'max : (⟨t * g', mul_mem htmem hg'mem⟩ : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
      by_cases hg0 : g' = 0
      · have : (⟨t * g', mul_mem htmem hg'mem⟩ : v.toValuationSubring) = 0 := Subtype.ext
          (by simp [hg0])
        rw [this]; exact Ideal.zero_mem _
      · exact CartierLocalPen12.mem_maximalIdeal_of_ord_pos v
          (by rw [v.ord_mul ht0 hg0, ht]; have := hg'; omega) _
    rw [← hresalg s]
    have heq : (⟨t * (algebraMap K F s * t⁻¹ + g'), hmem'⟩ : v.toValuationSubring) - ⟨algebraMap K
      F s, halgmem s⟩ =
        ⟨t * g', mul_mem htmem hg'mem⟩ := Subtype.ext (by simp [hval'])
    exact Ideal.Quotient.eq.mpr (by rw [heq]; exact htg'max)
end AlgebraicCurve.Place
end ProofImplementation
