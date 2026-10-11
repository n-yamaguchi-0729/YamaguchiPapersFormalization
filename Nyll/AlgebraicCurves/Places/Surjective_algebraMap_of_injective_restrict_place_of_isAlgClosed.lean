/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.Differentials.Uniformizer
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg
import Nyll.AlgebraicCurves.Differentials.OrdDifferential_map_eq
import Nyll.AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver
import Nyll.AlgebraicCurves.FunctionFields.Exists_mem_D_eq_smul_D_of_isCurveOver
import Nyll.AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import Nyll.AlgebraicCurves.FunctionFields.FiniteDimensional_adjoin_of_transcendental
import Nyll.AlgebraicCurves.Places.Place_exists_ord_neg_of_transcendental

/-!
# Surjective algebra Map of injective restrict place of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve IntermediateField

namespace P2mKcDegreeOneByInjectivePlaces

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_not_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : a ≠ 0)
    (hu : ¬IsUnit a) : 0 < v.ord (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu (by rw [pow_zero, mul_one]; exact u.isUnit)
  have hcoe : (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) =
      ((u : v.toValuationSubring) : F) * (π : F) ^ (n : ℤ) := by
    rw [zpow_natCast, Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using this
    have h2 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← h2]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact absurd (ord_neg_of_not_mem v hf) (not_lt.2 h)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  by_cases hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)
  · have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    exact le_of_eq this.symm
  · exact (ord_pos_of_not_isUnit v (fun h0 => hf0 (by simpa using congrArg Subtype.val h0)) hu).le

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {f : F} (hf : 0 < v.ord f) :
    ∃ h : f ∈ v.toValuationSubring,
      (⟨f, h⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  have hmem : f ∈ v.toValuationSubring := mem_of_ord_nonneg v hf.le
  refine ⟨hmem, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  change v.ord f = 0 at this
  omega

theorem isUnit_algebraMap (v : Place K F) {a : K} (ha : a ≠ 0) :
    IsUnit (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) := by
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h]
  exact (ha.isUnit).map _

theorem eq_of_ord_sub_algebraMap_pos (v : Place K F) (t : F) {c c' : K}
    (hc : 0 < v.ord (t - algebraMap K F c)) (hc' : 0 < v.ord (t - algebraMap K F c')) :
    c = c' := by
  by_contra hne
  obtain ⟨h1, hm1⟩ := mem_maximalIdeal_of_ord_pos v hc
  obtain ⟨h2, hm2⟩ := mem_maximalIdeal_of_ord_pos v hc'
  have hsub := Ideal.sub_mem _ hm2 hm1
  have hval : ((⟨t - algebraMap K F c', h2⟩ : v.toValuationSubring)
        - ⟨t - algebraMap K F c, h1⟩)
      = ⟨algebraMap K F (c - c'), v.algebraMap_mem' (c - c')⟩ := by
    apply Subtype.ext
    change (t - algebraMap K F c') - (t - algebraMap K F c) = algebraMap K F (c - c')
    rw [map_sub]
    ring
  rw [hval] at hsub
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hsub) (isUnit_algebraMap v (sub_ne_zero.mpr hne))

end PlaceFacts

section TotalRamification

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F']

theorem ramificationIndex_eq_finrank [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (hinj : Function.Injective (fun w : Place K F' => w.restrict F)) (w : Place K F') :
    w.ramificationIndex F = Module.finrank F F' := by
  have hfib : (w.restrict F).fiber F' = {w} := by
    ext w'
    rw [Place.mem_fiber, Finset.mem_singleton]
    exact ⟨fun h => hinj h, fun h => h ▸ rfl⟩
  have hid := Place.sum_ramificationIndex_mul_inertiaDeg (K := K) (F := F) (F' := F')
    (w.restrict F)
  rw [hfib, Finset.sum_singleton] at hid
  have hdeg : w.inertiaDeg F = 1 := by
    have h := w.deg_restrict_mul_inertiaDeg (F := F)
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed,
      one_mul] at h
    exact h
  rw [hdeg, Nat.cast_one, mul_one] at hid
  exact_mod_cast hid

end TotalRamification

section Finiteness

theorem differentialCoeff_D_regular {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F']
    [∀ w : Place K F', w.DCoordGenerates]
    (w : Place K F') (u : F') (_hu : u ≠ 0) (hord : w.ord u = 0) :
    w.differentialCoeff (KaehlerDifferential.D K F' u) = 0 ∨
      0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) := by
  right
  have humem : u ∈ w.toValuationSubring := mem_of_ord_nonneg w (le_of_eq hord.symm)
  obtain ⟨c, hc, hD⟩ := exists_mem_D_eq_smul_D_of_isCurveOver w w.ord_uniformizer humem
  rw [← Place.dCoord_eq] at hD
  rw [w.differentialCoeff_unique hD]
  exact ord_nonneg_of_mem w hc

theorem finite_place_of_one_lt (K F F' : Type) [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F']
    [Algebra.EssFiniteType K F'] [Module.Finite F F']
    (hinj : Function.Injective (fun w : Place K F' => w.restrict F))
    (hn : 1 < Module.finrank F F') : Finite (Place K F') := by
  classical
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  have hDC : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hDC' : ∀ w : Place K F', w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  have : HasCanonicalDivisor (K := K) (F := F') := hasCanonicalDivisor_of_isCurveOver
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  have he : ∀ w : Place K F', w.ramificationIndex F = Module.finrank F F' :=
    ramificationIndex_eq_finrank hinj
  have htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0 := fun w => by
    exact_mod_cast (w.ramificationIndex_pos (F := F)).ne'
  have hmap : ∀ w : Place K F', w.ordDifferential (KaehlerDifferential.map K K F F' ω₀)
      = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀
          + ((w.ramificationIndex F : ℤ) - 1) := fun w =>
    ordDifferential_map_eq (K := K) (F := F) (F' := F')
      (fun w u hu hord => differentialCoeff_D_regular w u hu hord) htame hω₀ w
  obtain ⟨D₀, hD₀⟩ := HasCanonicalDivisor.exists_divisor ω₀ hω₀
  have hD₁ : ∃ D₁ : Divisor K F',
      ∀ w, D₁ w = w.ordDifferential (KaehlerDifferential.map K K F F' ω₀) := by
    by_cases h0 : KaehlerDifferential.map K K F F' ω₀ = 0
    · refine ⟨0, fun w => ?_⟩
      rw [h0, Place.ordDifferential, Place.differentialCoeff_zero, Place.ord_zero]
      rfl
    · exact HasCanonicalDivisor.exists_divisor _ h0
  obtain ⟨D₁, hD₁⟩ := hD₁
  have hcover : (Set.univ : Set (Place K F')) ⊆
      (D₁.support : Set (Place K F')) ∪
        (fun w : Place K F' => w.restrict F) ⁻¹' (D₀.support : Set (Place K F)) := by
    intro w _
    by_contra hw
    simp only [Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_preimage,
      not_or, not_not] at hw
    have h := hmap w
    rw [← hD₁, ← hD₀, hw.1, hw.2, he w, mul_zero, zero_add] at h
    have h' : (Module.finrank F F' : ℤ) = 1 := by linarith
    have : Module.finrank F F' = 1 := by exact_mod_cast h'
    omega
  have hfin : (Set.univ : Set (Place K F')).Finite :=
    ((D₁.support.finite_toSet).union
      ((D₀.support.finite_toSet).preimage hinj.injOn)).subset hcover
  exact Set.finite_univ_iff.mp hfin

end Finiteness

section Infinitude

theorem infinite_place (K F' : Type) [Field K] [Field F'] [Algebra K F'] [IsAlgClosed K]
    [CharZero K] [IsCurveOver K F'] [Algebra.EssFiniteType K F'] : Infinite (Place K F') := by
  obtain ⟨t, ht, hfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F')
  have := hfin
  have key : ∀ c : K, ∃ w : Place K F', 0 < w.ord (t - algebraMap K F' c) := by
    intro c
    have hy : Transcendental K (t - algebraMap K F' c)⁻¹ := by
      intro halg
      apply ht
      have h1 : IsAlgebraic K (t - algebraMap K F' c) := IsAlgebraic.inv_iff.mp halg
      have h2 : IsAlgebraic K (t - algebraMap K F' c + algebraMap K F' c) :=
        h1.add (isAlgebraic_algebraMap c)
      simpa using h2
    have : FiniteDimensional K⟮(t - algebraMap K F' c)⁻¹⟯ F' :=
      finiteDimensional_adjoin_of_transcendental t hy
    obtain ⟨w, hw⟩ := Place.exists_ord_neg_of_transcendental (t - algebraMap K F' c)⁻¹ hy
    refine ⟨w, ?_⟩
    rw [Place.ord_inv] at hw
    omega
  choose w hw using key
  refine Infinite.of_injective w fun c c' h => ?_
  have h1 := hw c
  have h2 := hw c'
  rw [← h] at h2
  exact eq_of_ord_sub_algebraMap_pos (w c) t h1 h2

end Infinitude

end P2mKcDegreeOneByInjectivePlaces

open P2mKcDegreeOneByInjectivePlaces in
theorem _root_.AlgebraicCurve.surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
    (K F F' : Type) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
      [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F']
      [Algebra.EssFiniteType K F']
    [Module.Finite F F']
    (hinj : Function.Injective (fun w : Place K F' => w.restrict F)) :
    Function.Surjective (algebraMap F F') := by
  by_contra hns
  have hn : 1 < Module.finrank F F' := by
    have hpos : 0 < Module.finrank F F' := Module.finrank_pos
    rcases (Nat.succ_le_of_lt hpos).eq_or_lt with h1 | h1
    · exact absurd ((Algebra.finrank_eq_one_iff_bijective_algebraMap).mp h1.symm).2 hns
    · exact h1
  have := finite_place_of_one_lt K F F' hinj hn
  exact (infinite_place K F').not_finite ‹_›
end AlgebraicCurves.Places.Proofs.Surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
end ProofImplementation

attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
