/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Rational Localization
-/

namespace Rat

/-- The subring of `ℚ` whose denominators are prime to `p`; equivalently, the
localization of `ℤ` at the prime ideal `(p)` when `p` is prime. -/
def LocalizationAt (p : ℕ) : Subring ℚ where
  carrier := {q : ℚ | q.den.Coprime p}
  mul_mem' {a b} ha hb :=
    Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b) (ha.mul_left hb)
  one_mem' := by simp
  add_mem' {a b} ha hb :=
    Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b) (ha.mul_left hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

namespace LocalizationAt

theorem mem_iff_den_coprime {p : ℕ} (q : ℚ) :
    q ∈ Rat.LocalizationAt p ↔ q.den.Coprime p :=
  Iff.rfl

theorem mem_iff_not_dvd_den {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ Rat.LocalizationAt p ↔ ¬p ∣ q.den := by
  rw [mem_iff_den_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd]

theorem isUnit_iff_not_dvd_num {p : ℕ} (hp : p.Prime) (x : Rat.LocalizationAt p) :
    IsUnit x ↔ ¬p ∣ (x : ℚ).num.natAbs := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have hxy : (x : ℚ) * y = 1 := by
      rw [← Subring.coe_mul, hy, Subring.coe_one]
    have hx0 : (x : ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hxy
    have hyden : ¬p ∣ (y : ℚ).den := (mem_iff_not_dvd_den hp _).mp y.2
    rwa [eq_inv_of_mul_eq_one_right hxy, Rat.den_inv_of_ne_zero hx0] at hyden
  · intro hx
    have hx0 : (x : ℚ) ≠ 0 := by
      intro h0
      apply hx
      rw [h0, Rat.zero_num, Int.natAbs_zero]
      exact dvd_zero p
    have hmem : (x : ℚ)⁻¹ ∈ Rat.LocalizationAt p := by
      rw [mem_iff_not_dvd_den hp, Rat.den_inv_of_ne_zero hx0]
      exact hx
    exact IsUnit.of_mul_eq_one ⟨(x : ℚ)⁻¹, hmem⟩ (Subtype.ext (mul_inv_cancel₀ hx0))

/-- `Rat.LocalizationAt p` is the localization of `ℤ` at `(p)`. -/
theorem isLocalization {p : ℕ} (hp : p.Prime)
    [(Ideal.span {(p : ℤ)}).IsPrime] :
    IsLocalization.AtPrime (Rat.LocalizationAt p) (Ideal.span {(p : ℤ)}) := by
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · have hy : ¬(p : ℤ) ∣ (y : ℤ) := fun h =>
      Ideal.mem_primeCompl_iff.mp y.2 (Ideal.mem_span_singleton.mpr h)
    refine (isUnit_iff_not_dvd_num hp _).mpr fun h => hy (Int.natCast_dvd.mpr ?_)
    rwa [show ((algebraMap ℤ (Rat.LocalizationAt p) (y : ℤ) : Rat.LocalizationAt p) : ℚ) =
        ((y : ℤ) : ℚ) from rfl, Rat.num_intCast] at h
  · have hden : ¬(p : ℤ) ∣ ((z : ℚ).den : ℤ) := fun h =>
      (mem_iff_not_dvd_den hp _).mp z.2 (Int.natCast_dvd_natCast.mp h)
    refine ⟨((z : ℚ).num, ⟨((z : ℚ).den : ℤ), Ideal.mem_primeCompl_iff.mpr fun h =>
      hden (Ideal.mem_span_singleton.mp h)⟩), Subtype.ext ?_⟩
    change (z : ℚ) * (((z : ℚ).den : ℤ) : ℚ) = (((z : ℚ).num : ℤ) : ℚ)
    rw [Int.cast_natCast, Rat.mul_den_eq_num]
  · refine ⟨1, ?_⟩
    have h : ((x : ℤ) : ℚ) = ((y : ℤ) : ℚ) := congrArg Subtype.val hxy
    rw [Int.cast_inj.mp h]

private def denominatorMonoid (p : ℕ) : Submonoid ℤ where
  carrier := {z : ℤ | z ≠ 0 ∧ ((z : ℚ)⁻¹ ∈ Rat.LocalizationAt p)}
  one_mem' := by
    refine ⟨one_ne_zero, ?_⟩
    rw [Int.cast_one, inv_one, mem_iff_den_coprime]
    simp
  mul_mem' := by
    rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
    refine ⟨mul_ne_zero ha0 hb0, ?_⟩
    rw [Int.cast_mul, mul_inv]
    exact mul_mem ha hb

private lemma natCast_den_mem_denominatorMonoid {p : ℕ} {q : ℚ}
    (hq : q ∈ Rat.LocalizationAt p) : (q.den : ℤ) ∈ denominatorMonoid p := by
  refine ⟨Int.natCast_ne_zero.mpr q.den_nz, ?_⟩
  rw [mem_iff_den_coprime, Int.cast_natCast, Rat.inv_natCast_den_of_pos q.pos]
  exact hq

private scoped instance denominatorMonoid_isLocalization (p : ℕ) :
    IsLocalization (denominatorMonoid p) (Rat.LocalizationAt p) :=
  (isLocalization_iff (denominatorMonoid p) (Rat.LocalizationAt p)).mpr
    ⟨by
      rintro ⟨z, hz0, hzi⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨(z : ℚ)⁻¹, hzi⟩, Subtype.ext ?_⟩
      push_cast
      exact mul_inv_cancel₀ (Int.cast_ne_zero.mpr hz0),
    by
      rintro ⟨x, hx⟩
      refine ⟨⟨x.num, ⟨(x.den : ℤ), natCast_den_mem_denominatorMonoid hx⟩⟩, Subtype.ext ?_⟩
      push_cast
      exact (eq_div_iff (by exact_mod_cast x.den_nz)).mp (Rat.num_div_den x).symm,
    by
      intro a b h
      obtain rfl : a = b := Int.cast_injective (show ((a : ℚ)) = (b : ℚ) by
        exact_mod_cast congrArg Subtype.val h)
      exact ⟨1, rfl⟩⟩

/-- The rational localization has fraction field `ℚ`. -/
theorem isFractionRing (p : ℕ) : IsFractionRing (Rat.LocalizationAt p) ℚ := by
  let hloc := denominatorMonoid_isLocalization p
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (denominatorMonoid p) (Rat.LocalizationAt p) ℚ

/-- The rational localization is a principal ideal ring. -/
theorem isPrincipalIdealRing (p : ℕ) : IsPrincipalIdealRing (Rat.LocalizationAt p) := by
  let := denominatorMonoid_isLocalization p
  refine ⟨fun I => ?_⟩
  obtain ⟨d, hd⟩ := Submodule.IsPrincipal.principal (Ideal.under ℤ I)
  refine ⟨⟨algebraMap ℤ (Rat.LocalizationAt p) d, ?_⟩⟩
  conv_lhs =>
    rw [← IsLocalization.map_under (denominatorMonoid p) (Rat.LocalizationAt p) I]
  rw [hd]
  change Ideal.map _ (Ideal.span {d}) = _
  rw [Ideal.map_span, Set.image_singleton]

private theorem denominatorMonoid_eq_primeCompl {p : ℕ} (hp : p.Prime)
    [(Ideal.span {(p : ℤ)}).IsPrime] :
    denominatorMonoid p = (Ideal.span {(p : ℤ)}).primeCompl := by
  ext z
  change (z ≠ 0 ∧ ((z : ℚ)⁻¹ ∈ Rat.LocalizationAt p)) ↔ z ∉ Ideal.span {(p : ℤ)}
  constructor
  · rintro ⟨hz0, hden⟩ hmem
    rw [mem_iff_den_coprime, Rat.inv_intCast_den, ite_eq_right hz0] at hden
    rw [Ideal.mem_span_singleton] at hmem
    exact (hp.coprime_iff_not_dvd.mp hden.symm) (Int.natCast_dvd.mp hmem)
  · intro hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hz (Ideal.zero_mem _)
    refine ⟨hz0, ?_⟩
    rw [mem_iff_den_coprime, Rat.inv_intCast_den, ite_eq_right hz0]
    exact (hp.coprime_iff_not_dvd.mpr fun hd =>
      hz (Ideal.mem_span_singleton.mpr (Int.natCast_dvd.mpr hd))).symm

/-- The rational localization at a prime is a discrete valuation ring. -/
theorem isDiscreteValuationRing (p : ℕ) (hp : p.Prime) :
    IsDiscreteValuationRing (Rat.LocalizationAt p) := by
  have hpz : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hPprime : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hpz).mpr (Nat.prime_iff_prime_int.mp hp)
  have hloc : IsLocalization.AtPrime (Rat.LocalizationAt p) (Ideal.span {(p : ℤ)}) := by
    have h := denominatorMonoid_isLocalization p
    rwa [denominatorMonoid_eq_primeCompl hp] at h
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (fun h => hpz (Ideal.span_singleton_eq_bot.mp h)) (Rat.LocalizationAt p)

/-- The image of `p` is a uniformizer in the rational localization at `p`. -/
theorem irreducible_natCast (p : ℕ) (hp : p.Prime) :
    Irreducible ((p : ℕ) : Rat.LocalizationAt p) := by
  have hdvr : IsDiscreteValuationRing (Rat.LocalizationAt p) :=
    isDiscreteValuationRing p hp
  have hprime : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  have hloc := isLocalization (p := p) hp
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(p : ℤ)})
    (Rat.LocalizationAt p), Ideal.map_span, Set.image_singleton]
  rfl

end LocalizationAt

end Rat
