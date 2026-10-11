/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import EtaleFundamentalGroups.Kummer.Obstructions.LocalDerivative
import EtaleFundamentalGroups.Kummer.RootCovers.Local.Residue
import EtaleFundamentalGroups.Kummer.PureRadical.IntegralClosure

/-!
# Roots of unity in a tame pure-radical DVR extension

This file supplies the non-Henselian roots-of-unity input in the DVR form of
Stacks Project, Lemma 15.115.6 (tag `09EV`).  If a uniformizer acquires an
`n`-th root and `n` is a unit in the base DVR, then every `n`-th root of unity
in the resulting pure-radical field already belongs to the base fraction
field.

The proof uses the canonical power-basis normal form in the root algebra.  A
nonzero element with zero constant coefficient has uniformizer order not
divisible by `n`.  Applying this to the nonconstant part of a root of unity,
the linear term of the binomial expansion has the same order, whereas the
whole expression comes from the base DVR and hence has order divisible by
`n`, a contradiction.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v w

private theorem exists_add_pow_sub_pow_eq_linear_add_sq_mul
    {R : Type u} [CommRing R] (x y : R) (n : ℕ) (hn : 0 < n) :
    ∃ q : R,
      (x + y) ^ n - x ^ n =
        (n : R) * x ^ (n - 1) * y + y ^ 2 * q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction k with
  | zero =>
      exact ⟨0, by simp⟩
  | succ k ih =>
      obtain ⟨q, hq⟩ := ih (Nat.succ_pos k)
      refine ⟨((k + 1 : ℕ) : R) * x ^ k + q * (x + y), ?_⟩
      rw [pow_succ (x + y) (k + 1), pow_succ x (k + 1)]
      rw [show
        (x + y) ^ (k + 1) * (x + y) - x ^ (k + 1) * x =
          ((x + y) ^ (k + 1) - x ^ (k + 1)) * (x + y) +
            x ^ (k + 1) * y by ring]
      rw [hq]
      push_cast
      ring

/-- In a tame pure-uniformizer extension of DVR fraction fields, every root
of unity whose order divides the radical degree descends to the base field.

All hypotheses are source data of the pure-radical presentation.  In
particular, no Henselian or roots-of-unity descent assumption is used. -/
theorem rootOfUnity_mem_fractionBase_of_dvr_pureRadical
    {V : Type u} {K : Type v} {L : Type w}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Field L]
    [Algebra V K] [IsFractionRing V K]
    [Algebra K L] [Algebra V L] [IsScalarTower V K L]
    [FiniteDimensional K L]
    {n : ℕ} (hn : 0 < n) (hnUnit : IsUnit (n : V))
    (pi : V) (hpi : Prime pi)
    (alpha : L)
    (hdegree : Module.finrank K L = n)
    (halphaPow : alpha ^ n = algebraMap K L (algebraMap V K pi))
    (hgen : IntermediateField.adjoin K {alpha} = ⊤)
    (zeta : L) (hzetaPow : zeta ^ n = 1) :
    zeta ∈ Set.range (algebraMap K L) := by
  let p : V[X] := X ^ n - C pi
  let R := AdjoinRoot p
  have hn0 : n ≠ 0 := hn.ne'
  have hpMonic : p.Monic := monic_X_pow_sub_C pi hn0
  have hpIrreducibleMap :
      Irreducible (p.map (algebraMap V K)) := by
    simpa [p] using
      irreducible_X_pow_sub_C_fractionRing_of_prime hpi hn
  have hpIrreducible : Irreducible p :=
    (hpMonic.irreducible_iff_irreducible_map_fraction_map).2
      hpIrreducibleMap
  have hpPrime : Prime p := hpIrreducible.prime
  let : IsDomain R := AdjoinRoot.isDomain_of_prime hpPrime
  have hpiMem : pi ∈ IsLocalRing.maximalIdeal V := by
    exact (IsLocalRing.mem_maximalIdeal _).2 hpi.not_isUnit
  let : IsLocalRing R :=
    isLocalRing_adjoinRoot_X_pow_sub_C hn hpiMem
  let : Module.FaithfullyFlat V R :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hn pi
  let phi : R →ₐ[V] L :=
    pureRadicalAdjoinRootToField pi alpha halphaPow
  let : Algebra R L := phi.toRingHom.toAlgebra
  let : IsScalarTower V R L :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (phi.commutes a).symm
  let : IsFractionRing R L :=
    isFractionRing_adjoinRoot_of_pureRadical
      hn pi alpha hdegree halphaPow hgen
  have hpiNe : pi ≠ 0 := hpi.ne_zero
  have hpiIrreducible : Irreducible pi := hpi.irreducible
  have hmaxV :
      IsLocalRing.maximalIdeal V = Ideal.span {pi} :=
    hpiIrreducible.maximalIdeal_eq
  have hmaxR :
      IsLocalRing.maximalIdeal R =
        Ideal.span {AdjoinRoot.root p} := by
    rw [maximalIdeal_adjoinRoot_X_pow_sub_C hn hpiMem]
    apply le_antisymm
    · apply sup_le
      · rw [hmaxV, Ideal.map_span]
        simp only [Set.image_singleton]
        rw [show AdjoinRoot.of p pi = AdjoinRoot.root p ^ n by
          simpa [p] using (adjoinRoot_root_pow n pi).symm]
        rw [Ideal.span_le]
        rintro _ (rfl : _ = AdjoinRoot.root p ^ n)
        exact Ideal.pow_mem_of_mem (Ideal.span {AdjoinRoot.root p})
          (Ideal.mem_span_singleton_self _) n hn
      · exact le_rfl
    · exact le_sup_right
  have hrootNe : AdjoinRoot.root p ≠ 0 := by
    intro hroot
    have hmapPiNe : algebraMap V R pi ≠ 0 := by
      intro hzero
      apply hpiNe
      apply FaithfulSMul.algebraMap_injective V R
      simpa using hzero
    apply hmapPiNe
    rw [show algebraMap V R pi = AdjoinRoot.root p ^ n by
      change AdjoinRoot.of p pi = AdjoinRoot.root p ^ n
      simpa [p] using (adjoinRoot_root_pow n pi).symm,
      hroot, zero_pow hn0]
  have hRNotField : ¬ IsField R := by
    intro hfield
    have hbot : IsLocalRing.maximalIdeal R = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    have : AdjoinRoot.root p ∈ (⊥ : Ideal R) := by
      rw [← hbot, hmaxR]
      exact Ideal.mem_span_singleton_self _
    exact hrootNe (by simpa using this)
  have hprincipal :
      Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) := by
    exact ⟨AdjoinRoot.root p, hmaxR⟩
  let : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hRNotField).out 5 1).mp hprincipal
  let : Module.Finite V R := hpMonic.finite_adjoinRoot
  let : Algebra.IsIntegral V R := Algebra.IsIntegral.of_finite V R
  let coeffZero : R →ₗ[V] V :=
    (Polynomial.lcoeff V 0).comp (AdjoinRoot.modByMonicHom hpMonic)
  have hresidueCoeff (z : R) :
      IsLocalRing.residue R z =
        IsLocalRing.residue R (algebraMap V R (coeffZero z)) := by
    have hrootMem :
        AdjoinRoot.root p ∈ IsLocalRing.maximalIdeal R := by
      rw [hmaxR]
      exact Ideal.mem_span_singleton_self _
    have hrootResidue :
        IsLocalRing.residue R (AdjoinRoot.root p) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 hrootMem
    let q : V[X] := AdjoinRoot.modByMonicHom hpMonic z
    have hzMk : AdjoinRoot.mk p q = z :=
      AdjoinRoot.mk_leftInverse hpMonic z
    change IsLocalRing.residue R z =
      IsLocalRing.residue R (algebraMap V R (q.coeff 0))
    rw [← hzMk]
    change IsLocalRing.residue R (AdjoinRoot.mk p q) =
      IsLocalRing.residue R (AdjoinRoot.of p (q.coeff 0))
    calc
      IsLocalRing.residue R (AdjoinRoot.mk p q) =
          IsLocalRing.residue R
            (AdjoinRoot.mk p (X * q.divX + C (q.coeff 0))) := by
        rw [Polynomial.X_mul_divX_add]
      _ = IsLocalRing.residue R (AdjoinRoot.of p (q.coeff 0)) := by
        rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
          map_add, map_mul, hrootResidue, zero_mul, zero_add]
  have hcoeffZero_algebraMap (a : V) :
      coeffZero (algebraMap V R a) = a := by
    change
      (AdjoinRoot.modByMonicHom hpMonic (AdjoinRoot.of p a)).coeff 0 = a
    rw [show AdjoinRoot.of p a = AdjoinRoot.mk p (C a) by rfl,
      AdjoinRoot.modByMonicHom_mk,
      (modByMonic_eq_self_iff hpMonic).2]
    · simp
    · rw [degree_X_pow_sub_C hn pi]
      exact degree_C_lt.trans_le (by exact_mod_cast hn)
  have hcoeffZero_smul (a : V) (z : R) :
      coeffZero (algebraMap V R a * z) = a * coeffZero z := by
    simpa [Algebra.smul_def] using coeffZero.map_smul a z
  have hcoeffZeroUnit {z : R} (hz : IsUnit z) :
      IsUnit (coeffZero z) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro hzero
    have hzResidueNe : IsLocalRing.residue R z ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit z).2 hz
    apply hzResidueNe
    rw [hresidueCoeff z, ← IsLocalRing.ResidueField.map_residue,
      hzero, map_zero]
  have hrootIrreducible : Irreducible (AdjoinRoot.root p) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
      (AdjoinRoot.root p) hrootNe hmaxR
  have hzetaIntegral : IsIntegral V zeta := by
    refine ⟨X ^ n - C 1, monic_X_pow_sub_C 1 hn0, ?_⟩
    simp [hzetaPow]
  let b : R := IsIntegralClosure.mk' R zeta hzetaIntegral
  have hbL : algebraMap R L b = zeta :=
    IsIntegralClosure.algebraMap_mk' R zeta hzetaIntegral
  have hbPow : b ^ n = 1 := by
    apply IsFractionRing.injective R L
    rw [map_pow, hbL, hzetaPow, map_one]
  have hbUnit : IsUnit b := by
    rw [isUnit_iff_exists_inv]
    refine ⟨b ^ (n - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel hn, hbPow]
  let a : V := coeffZero b
  have haUnit : IsUnit a := hcoeffZeroUnit hbUnit
  let d : R := b - algebraMap V R a
  have hcoeffD : coeffZero d = 0 := by
    simp [d, a, hcoeffZero_algebraMap]
  by_cases hd : d = 0
  · refine ⟨algebraMap V K a, ?_⟩
    have hbEq : b = algebraMap V R a := by
      apply sub_eq_zero.mp
      simpa only [d] using hd
    calc
      algebraMap K L (algebraMap V K a) = algebraMap V L a :=
        (IsScalarTower.algebraMap_apply V K L a).symm
      _ = algebraMap R L (algebraMap V R a) := by
        rw [IsScalarTower.algebraMap_apply V R L]
      _ = algebraMap R L b := by rw [hbEq]
      _ = zeta := hbL
  · obtain ⟨s, ud, hdFactor⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        hd hrootIrreducible
    have hsPos : 0 < s := by
      apply Nat.pos_of_ne_zero
      intro hs
      have hdUnit : IsUnit d := by
        rw [hdFactor, hs, pow_zero, mul_one]
        exact ud.isUnit
      exact (hcoeffZeroUnit hdUnit).ne_zero hcoeffD
    have hsNotDvd : ¬ n ∣ s := by
      rintro ⟨q, rfl⟩
      have hrootPow :
          AdjoinRoot.root p ^ n = algebraMap V R pi := by
        change AdjoinRoot.root p ^ n = AdjoinRoot.of p pi
        simpa [p] using adjoinRoot_root_pow n pi
      have hdFactor' :
          d = algebraMap V R (pi ^ q) * (ud : R) := by
        rw [hdFactor, pow_mul, hrootPow, map_pow]
        ring
      apply (mul_ne_zero (pow_ne_zero q hpiNe)
        (hcoeffZeroUnit ud.isUnit).ne_zero)
      rw [← hcoeffZero_smul, ← hdFactor', hcoeffD]
    obtain ⟨q, hq⟩ :=
      exists_add_pow_sub_pow_eq_linear_add_sq_mul
        (algebraMap V R a) d n hn
    have hbDecomp : algebraMap V R a + d = b := by
      simp [d]
    have hleadUnit : IsUnit
        ((n : R) * (algebraMap V R a) ^ (n - 1) * (ud : R)) :=
      ((hnUnit.map (algebraMap V R)).mul
        ((haUnit.map (algebraMap V R)).pow (n - 1))).mul ud.isUnit
    let leadUnit : Rˣ := hleadUnit.unit
    have hlead :
        (n : R) * (algebraMap V R a) ^ (n - 1) * d =
          (leadUnit : R) * AdjoinRoot.root p ^ s := by
      rw [hdFactor]
      rw [show (leadUnit : R) =
          (n : R) * (algebraMap V R a) ^ (n - 1) * (ud : R) by
        exact hleadUnit.unit_spec]
      ring
    have hleftBase :
        (algebraMap V R a + d) ^ n - (algebraMap V R a) ^ n =
          algebraMap V R (1 - a ^ n) := by
      rw [hbDecomp, hbPow, map_sub, map_one, map_pow]
    have hqTermValGt :
        IsDiscreteValuationRing.addVal R
              ((leadUnit : R) * AdjoinRoot.root p ^ s) <
          IsDiscreteValuationRing.addVal R (d ^ 2 * q) := by
      rw [IsDiscreteValuationRing.addVal_def' leadUnit hrootIrreducible s]
      by_cases hqZero : q = 0
      · rw [hqZero, mul_zero, IsDiscreteValuationRing.addVal_zero]
        exact ENat.natCast_lt_top s
      · obtain ⟨k, uq, hqFactor⟩ :=
          IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
            hqZero hrootIrreducible
        let remainderUnit : Rˣ := ud ^ 2 * uq
        have hrem :
            d ^ 2 * q =
              (remainderUnit : R) * AdjoinRoot.root p ^ (2 * s + k) := by
          rw [hdFactor, hqFactor]
          change
            ((ud : R) * AdjoinRoot.root p ^ s) ^ 2 *
                ((uq : R) * AdjoinRoot.root p ^ k) =
              ((ud : R) ^ 2 * (uq : R)) *
                AdjoinRoot.root p ^ (2 * s + k)
          simp only [mul_pow, pow_add, pow_mul]
          ring
        rw [hrem,
          IsDiscreteValuationRing.addVal_def' remainderUnit
            hrootIrreducible (2 * s + k)]
        exact_mod_cast (by omega : s < 2 * s + k)
    have hleftVal :
        IsDiscreteValuationRing.addVal R
            ((algebraMap V R a + d) ^ n -
              (algebraMap V R a) ^ n) = s := by
      rw [hq, hlead]
      calc
        IsDiscreteValuationRing.addVal R
            ((leadUnit : R) * AdjoinRoot.root p ^ s + d ^ 2 * q) =
            IsDiscreteValuationRing.addVal R
              ((leadUnit : R) * AdjoinRoot.root p ^ s) :=
          (IsDiscreteValuationRing.addVal R).map_add_eq_of_lt_left
            hqTermValGt
        _ = s := IsDiscreteValuationRing.addVal_def'
          leadUnit hrootIrreducible s
    have hbaseNe : 1 - a ^ n ≠ 0 := by
      intro hzero
      rw [hleftBase, hzero, map_zero,
        IsDiscreteValuationRing.addVal_zero] at hleftVal
      exact (ENat.natCast_ne_top s) hleftVal.symm
    obtain ⟨k, uk, hkFactor⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        hbaseNe hpiIrreducible
    let baseUnit : Rˣ := Units.map (algebraMap V R) uk
    have hbaseFactor :
        algebraMap V R (1 - a ^ n) =
          (baseUnit : R) * AdjoinRoot.root p ^ (n * k) := by
      rw [hkFactor, map_mul, map_pow]
      simp only [baseUnit, Units.coe_map]
      rw [show algebraMap V R pi = AdjoinRoot.root p ^ n by
        change AdjoinRoot.of p pi = AdjoinRoot.root p ^ n
        simpa [p] using (adjoinRoot_root_pow n pi).symm,
        pow_mul]
      rfl
    have hsEq : s = n * k := by
      have := hleftVal
      rw [hleftBase, hbaseFactor,
        IsDiscreteValuationRing.addVal_def' baseUnit
          hrootIrreducible (n * k)] at this
      exact (ENat.natCast_inj.mp this).symm
    exact (hsNotDvd ⟨k, hsEq⟩).elim

end EtaleFundamentalGroups.Kummer
