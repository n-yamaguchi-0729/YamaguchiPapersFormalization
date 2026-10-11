/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.LocalGeometry.HeightOne.PrincipalDVR
import EtaleFundamentalGroups.Kummer.LocalGeometry.Regular.PairPrimeDichotomy
import EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.StandardCompletion

/-!
# The retained root divisor over a completed regular pair is a DVR

Mathlib does not currently provide a global `IsNoetherianRing` instance for
the maximal-adic completion used here.  The root-divisor argument only needs
the corresponding height-one localization to be a DVR.

For the first parameter of a completed regular pair, maximal-adic
separatedness rules out a nonzero prime strictly below its principal prime.
Thus its localization has Krull dimension at most one; its maximal ideal is
principal, so the Noetherian-free local criterion makes it a DVR.  Adjoining
a positive root of that parameter and localizing at the root prime is then
the usual pure-root DVR construction over this local base.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing
open Polynomial
open RingTheory.Sequence

universe u

/-- In a maximal-adically separated local domain, a principal prime has no
nonzero prime strictly below it.  Repeated divisibility by its generator
would otherwise put a fixed nonzero element in every power of the maximal
ideal. -/
private theorem prime_eq_span_of_nonzero_le_span_of_isHausdorff
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    [IsHausdorff (maximalIdeal R) R]
    {x : R} (hx : Prime x)
    (P : Ideal R) [P.IsPrime]
    (hPne : P ≠ ⊥) (hPle : P ≤ Ideal.span ({x} : Set R)) :
    P = Ideal.span ({x} : Set R) := by
  apply le_antisymm hPle
  rw [Ideal.span_le, Set.singleton_subset_iff]
  by_contra hxP
  obtain ⟨a, haP, haNe⟩ : ∃ a : R, a ∈ P ∧ a ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hPne
    rw [eq_bot_iff]
    intro a ha
    exact hall a ha
  have hfactor : ∀ n : ℕ, ∃ b : R, b ∈ P ∧ a = x ^ n * b := by
    intro n
    induction n with
    | zero =>
        exact ⟨a, haP, by simp⟩
    | succ n ih =>
        obtain ⟨b, hbP, hab⟩ := ih
        have hbSpan : b ∈ Ideal.span ({x} : Set R) := hPle hbP
        rw [Ideal.mem_span_singleton] at hbSpan
        obtain ⟨c, hc⟩ := hbSpan
        have hcP : c ∈ P := by
          apply ((inferInstance : P.IsPrime).mem_or_mem ?_).resolve_left hxP
          rw [← hc]
          exact hbP
        refine ⟨c, hcP, ?_⟩
        calc
          a = x ^ n * b := hab
          _ = x ^ n * (x * c) := by rw [hc]
          _ = x ^ (n + 1) * c := by rw [pow_succ, mul_assoc]
  have hxMax : x ∈ maximalIdeal R :=
    (mem_maximalIdeal x).mpr hx.not_isUnit
  have haPow : ∀ n : ℕ, a ∈ maximalIdeal R ^ n := by
    intro n
    obtain ⟨b, -, hab⟩ := hfactor n
    rw [hab]
    exact (maximalIdeal R ^ n).mul_mem_right b
      (Ideal.pow_mem_pow hxMax n)
  have haZero : a = 0 :=
    IsHausdorff.haus (I := maximalIdeal R) inferInstance a fun n ↦ by
      exact SModEq.zero.2 <| by
        simpa [Ideal.smul_top_eq_map] using haPow n
  exact haNe haZero

/-- The localization at a prime generator in a maximal-adically separated
local domain is a DVR, without a Noetherian hypothesis on the ring.

The only dimension input is generated internally: prime contraction for a
localization and the preceding separatedness lemma show that every nonzero
prime of the localization is maximal. -/
theorem exists_isDiscreteValuationRing_localizationAtPrime_of_prime_isHausdorff
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    [IsHausdorff (maximalIdeal R) R]
    {x : R} (hx : Prime x) :
    let q := Ideal.span ({x} : Set R)
    letI : q.IsPrime := Ideal.isPrime_span_singleton_of_prime hx
    let V := Localization.AtPrime q
    ∃ hdomain : IsDomain V,
      letI : IsDomain V := hdomain
      IsDiscreteValuationRing V := by
  dsimp only
  let q := Ideal.span ({x} : Set R)
  let : q.IsPrime := Ideal.isPrime_span_singleton_of_prime hx
  let V := Localization.AtPrime q
  have hdomain : IsDomain V :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      V q.primeCompl_le_nonZeroDivisors
  let : IsDomain V := hdomain
  have hdim : Ring.KrullDimLE 1 V := by
    apply Ring.KrullDimLE.mk₁'
    intro P hPne hPPrime
    let : P.IsPrime := hPPrime
    let p : Ideal R := P.under R
    let : p.IsPrime := hPPrime.comap (algebraMap R V)
    have hpNe : p ≠ ⊥ := by
      exact ne_of_gt <|
        IsLocalization.bot_lt_under_prime
          (M := q.primeCompl) (S := V)
          q.primeCompl_le_nonZeroDivisors P hPne
    have hpLe : p ≤ q := by
      intro r hr
      by_contra hrq
      have hrUnit : IsUnit (algebraMap R V r) :=
        IsLocalization.map_units V (⟨r, hrq⟩ : q.primeCompl)
      have hrP : algebraMap R V r ∈ P := hr
      exact hPPrime.ne_top (P.eq_top_of_isUnit_mem hrP hrUnit)
    have hpEq : p = q :=
      prime_eq_span_of_nonzero_le_span_of_isHausdorff
        hx p hpNe hpLe
    have hPMap : p.map (algebraMap R V) = P :=
      IsLocalization.map_under q.primeCompl V P
    have hPEq : P = maximalIdeal V := by
      calc
        P = p.map (algebraMap R V) := hPMap.symm
        _ = q.map (algebraMap R V) := by rw [hpEq]
        _ = maximalIdeal V :=
          IsLocalization.AtPrime.map_eq_maximalIdeal q V
    rw [hPEq]
    exact maximalIdeal.isMaximal V
  let : Ring.KrullDimLE 1 V := hdim
  have hqNe : q ≠ ⊥ := by
    intro hq
    have hxZero : x = 0 := by
      have : x ∈ q := Ideal.mem_span_singleton_self x
      rw [hq, Ideal.mem_bot] at this
      exact this
    exact hx.ne_zero hxZero
  have hnotField : ¬ IsField V :=
    IsLocalization.AtPrime.not_isField R hqNe V
  have hmaxV :
      maximalIdeal V =
        Ideal.span ({algebraMap R V x} : Set V) := by
    calc
      maximalIdeal V = q.map (algebraMap R V) :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal q V).symm
      _ = Ideal.span ({algebraMap R V x} : Set V) := by
        simp only [q, Ideal.map_span, Set.image_singleton]
  have hprincipal : (maximalIdeal V).IsPrincipal := by
    refine ⟨algebraMap R V x, ?_⟩
    simpa using hmaxV
  exact ⟨hdomain,
    isDiscreteValuationRing_of_krullDimLE_one_of_maximalIdeal_isPrincipal
      hnotField hprincipal⟩

/-- A positive pure-root localization is a DVR as soon as the localization
of the radicand at its principal prime is a DVR.  Unlike the older global
wrapper, this statement does not require `IsRegularRing R`. -/
theorem
    exists_adjoinRootLocalizationAtRootPrime_isDiscreteValuationRing_of_baseDVR
    {R : Type u} [CommRing R] [IsDomain R]
    {N : ℕ} (hN : 0 < N) {p : R} (hp : Prime p)
    (hbaseDVR :
      let P := Ideal.span ({p} : Set R)
      letI : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
      IsDiscreteValuationRing (Localization.AtPrime P)) :
    let P := Ideal.span ({p} : Set R)
    let D := AdjoinRoot (X ^ N - C p)
    let q := Ideal.span
      ({AdjoinRoot.root (X ^ N - C p)} : Set D)
    letI : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    letI : q.IsPrime := Ideal.isPrime_span_singleton_of_prime
      (prime_adjoinRoot_root_of_prime hN hp)
    letI : q.LiesOver P := span_root_liesOver_span_radicand hN hp
    let V := Localization.AtPrime P
    letI : Algebra V (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver P q
    ∃ hdomain : IsDomain (Localization.AtPrime q),
      letI : IsDomain (Localization.AtPrime q) := hdomain
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  dsimp only at hbaseDVR ⊢
  let P := Ideal.span ({p} : Set R)
  let D := AdjoinRoot (X ^ N - C p)
  let q := Ideal.span
    ({AdjoinRoot.root (X ^ N - C p)} : Set D)
  let : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  let : q.IsPrime := Ideal.isPrime_span_singleton_of_prime
    (prime_adjoinRoot_root_of_prime hN hp)
  let : q.LiesOver P := span_root_liesOver_span_radicand hN hp
  let V := Localization.AtPrime P
  let : IsDiscreteValuationRing V := hbaseDVR
  let pV : V := algebraMap R V p
  have hmaxV : maximalIdeal V = Ideal.span ({pV} : Set V) := by
    calc
      maximalIdeal V = P.map (algebraMap R V) :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal P V).symm
      _ = Ideal.span ({pV} : Set V) := by
        simp [P, pV, Ideal.map_span]
  have hpVne : pV ≠ 0 := by
    intro hpVzero
    apply hp.ne_zero
    exact (IsLocalization.injective V P.primeCompl_le_nonZeroDivisors)
      (by simpa only [map_zero] using hpVzero)
  have hpV : Prime pV :=
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
      pV hpVne hmaxV).prime
  let Rn := AdjoinRoot (X ^ N - C pV)
  let : IsDomain Rn :=
    isDomain_adjoinRoot_X_pow_sub_C_of_prime hN pV hpV
  let : IsDiscreteValuationRing Rn :=
    isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hN pV hpV
  let : Algebra D Rn :=
    adjoinRootLocalizationBaseChangeAlgebra R N p hp
  let W := Localization.AtPrime q
  let : Algebra V W :=
    Localization.AtPrime.algebraOfLiesOver P q
  let eLocal : Rn ≃ₐ[V] W :=
    adjoinRootLocalizationAtRootPrimeAlgEquiv hN hp
  have hdomain : IsDomain W :=
    eLocal.symm.toMulEquiv.isDomain Rn
  let : IsDomain W := hdomain
  exact ⟨hdomain,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      eLocal.toRingEquiv⟩

/-- Application form for a maximal-adic completion of a regular pair.  The
completed base is not assumed Noetherian: its first-parameter localization
is constructed as a DVR from regular-pair geometry and separatedness, then
the selected root localization is constructed over that DVR. -/
theorem
    exists_maximalAdicCompletion_regularPair_oneRootPrime_localDVR
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x z : R}
    (hreg : IsRegular R [x, z])
    (hgen : Ideal.ofList [x, z] = maximalIdeal R)
    {N : ℕ} (hN : 0 < N) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let xhat : Rhat := algebraMap R Rhat x
    let Dhat := AdjoinRoot (X ^ N - C xhat)
    let qhat := Ideal.span
      ({AdjoinRoot.root (X ^ N - C xhat)} : Set Dhat)
    letI : IsDomain Rhat :=
      (maximalAdicCompletion_regularPair_geometry hreg hgen).1
    letI : qhat.IsPrime := Ideal.isPrime_span_singleton_of_prime
      (prime_adjoinRoot_root_of_prime hN
        (maximalAdicCompletion_regularPair_geometry hreg hgen).2.2.2.1)
    ∃ hdomain : IsDomain (Localization.AtPrime qhat),
      letI : IsDomain (Localization.AtPrime qhat) := hdomain
      IsDiscreteValuationRing (Localization.AtPrime qhat) := by
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  let xhat : Rhat := algebraMap R Rhat x
  let Dhat := AdjoinRoot (X ^ N - C xhat)
  let qhat := Ideal.span
    ({AdjoinRoot.root (X ^ N - C xhat)} : Set Dhat)
  have hgeometry := maximalAdicCompletion_regularPair_geometry hreg hgen
  let : IsDomain Rhat := hgeometry.1
  have hxhat : Prime xhat := hgeometry.2.2.2.1
  let : qhat.IsPrime := Ideal.isPrime_span_singleton_of_prime
    (prime_adjoinRoot_root_of_prime hN hxhat)
  obtain ⟨hbaseDomain, hbaseDVR⟩ :=
    exists_isDiscreteValuationRing_localizationAtPrime_of_prime_isHausdorff
      hxhat
  let qbase := Ideal.span ({xhat} : Set Rhat)
  let : qbase.IsPrime := Ideal.isPrime_span_singleton_of_prime hxhat
  let : IsDomain (Localization.AtPrime qbase) := hbaseDomain
  rcases
      exists_adjoinRootLocalizationAtRootPrime_isDiscreteValuationRing_of_baseDVR
        hN hxhat hbaseDVR with
    ⟨hrootDomain, hrootDVR⟩
  exact ⟨hrootDomain, hrootDVR⟩

end EtaleFundamentalGroups.Kummer

end
