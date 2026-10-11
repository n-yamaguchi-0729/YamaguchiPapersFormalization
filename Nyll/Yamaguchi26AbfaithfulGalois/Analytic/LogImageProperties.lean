/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLog
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogImage
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogReduced
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPadicIntMap
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# The image of the principal-unit logarithm

Openness, closedness, torsion-freeness, and separation of the actual
logarithm image in Section 3 of [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1).
-/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

/-- The actual image `Λ_K = log(U_K)` is both open and closed in the
additive group of the complete field. -/
theorem principal_unit_log_image_open_closed
    {K : Type u} [Field K] [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let Λ : Set K := Set.range
      (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (completeDVFOfWithZeroValuation v) 1 =>
        (principalUnitLogOfMixedChar v p u).toAdd)
    IsOpen Λ ∧ IsClosed Λ := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let f : Additive
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v) 1) →+ K :=
    (principalUnitLogOfMixedChar v p).toAdditiveLeft
  let L : AddSubgroup K := f.range
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let e : K ≃ₜ K := Homeomorph.mulLeft₀ ((p : K) ^ 2) (pow_ne_zero 2 hp)
  let B : Set K := e '' (v.valuationSubring : Set K)
  have hBopen : IsOpen B :=
    e.isOpen_image.mpr (show IsOpen (v.valuationSubring : Set K) from
      Valued.isOpen_valuationSubring K)
  have h0B : (0 : K) ∈ B := by
    refine ⟨0, (v.valuationSubring).zero_mem, ?_⟩
    change (p : K) ^ 2 * 0 = 0
    exact mul_zero _
  have hBsub : B ⊆ (L : Set K) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨u, hu⟩ := exists_principalUnit_log_eq_natCast_sq_mul v p
      (⟨a, ha⟩ : v.valuationSubring)
    apply AddMonoidHom.mem_range.mpr
    refine ⟨Additive.ofMul u, ?_⟩
    change (principalUnitLogOfMixedChar v p u).toAdd = (p : K) ^ 2 * a
    exact hu
  have hLopen : IsOpen (L : Set K) :=
    AddSubgroup.isOpen_of_mem_nhds L
      (Filter.mem_of_superset (hBopen.mem_nhds h0B) hBsub)
  have hLclosed : IsClosed (L : Set K) := AddSubgroup.isClosed_of_isOpen L hLopen
  change IsOpen (L : Set K) ∧ IsClosed (L : Set K)
  exact ⟨hLopen, hLclosed⟩

/-- The actual logarithm image is torsion-free for its canonical
`ℤ_p`-module structure. -/
theorem principal_unit_log_image_torsion_free
    {K : Type u} [Field K] [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    let Λ : Set K := Set.range
      (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (completeDVFOfWithZeroValuation v) 1 =>
        (principalUnitLogOfMixedChar v p u).toAdd)
    ∀ (a : ℤ_[p]) (x : K), x ∈ Λ →
      padicIntToFieldOfMixedChar v p a * x = 0 → a = 0 ∨ x = 0 := by
  let f : ℤ_[p] →+* K := padicIntToFieldOfMixedChar v p
  have hf : Function.Injective f := by
    apply (RingHom.injective_iff_ker_eq_bot f).mpr
    by_contra hker
    obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
    have hpow : (p : ℤ_[p]) ^ n ∈ RingHom.ker f := by
      rw [hn]
      exact Ideal.subset_span (by simp)
    have hzero : f ((p : ℤ_[p]) ^ n) = 0 := RingHom.mem_ker.mp hpow
    have hpKpow : (p : K) ^ n = 0 := by
      simpa only [map_pow, map_natCast] using hzero
    have hpK : (p : K) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    exact (pow_ne_zero n hpK) hpKpow
  intro Λ a x _ hax
  rcases mul_eq_zero.mp hax with ha | hx
  · left
    apply hf
    simpa only [map_zero] using ha
  · exact Or.inr hx

/-- No nonzero field element lies in every `p^m` multiple of the
principal-unit logarithm image. -/
theorem principal_unit_log_image_separated
    {K : Type u} [Field K] [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (x : K)
    (hx : ∀ m : ℕ,
      ∃ u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (completeDVFOfWithZeroValuation v) 1,
        x = (p : K) ^ m * (principalUnitLogOfMixedChar v p u).toAdd) :
    x = 0 := by
  by_contra hxne
  obtain ⟨k, _, hk⟩ := exists_principalUnitLog_denominator_min_bound v p
  let d : ℤ := ((k + 1 : ℕ) : ℤ) - (v.residueRamificationIndex p : ℤ) *
    (padicValNat p (k + 1) : ℤ)
  let V := ofWithZeroValuation v
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let ep : ℤ := V.val (Units.mk0 (p : K) hp)
  have hep : 0 < ep := by
    change 0 < -WithZero.log (v (p : K))
    exact neg_pos.mpr (v.log_natCast_residueChar_neg p)
  let vx : ℤ := V.val (Units.mk0 x hxne)
  let m : ℕ := Int.toNat (vx - d) + 1
  have hm : vx - d < (m : ℤ) := by
    dsimp [m]
    omega
  obtain ⟨u, hu⟩ := hx m
  let y : K := (principalUnitLogOfMixedChar v p u).toAdd
  have hyne : y ≠ 0 := by
    intro hy
    apply hxne
    rw [hu, show (principalUnitLogOfMixedChar v p u).toAdd = 0 from hy, mul_zero]
  have hylower : d ≤ V.val (Units.mk0 y hyne) := hk u hyne
  have hunit : Units.mk0 x hxne = (Units.mk0 (p : K) hp) ^ m * Units.mk0 y hyne := by
    apply Units.ext
    change x = (p : K) ^ m * y
    exact hu
  have hvx : vx = (m : ℤ) * ep + V.val (Units.mk0 y hyne) := by
    dsimp [vx, ep]
    rw [hunit, V.val_mul, V.val_pow]
  have hmle : (m : ℤ) ≤ (m : ℤ) * ep := by
    calc
      (m : ℤ) = (m : ℤ) * 1 := by ring
      _ ≤ (m : ℤ) * ep :=
        mul_le_mul_of_nonneg_left (by omega) (by exact_mod_cast Nat.zero_le m)
  omega

end Yamaguchi26AbfaithfulGalois
