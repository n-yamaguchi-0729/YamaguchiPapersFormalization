/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CompleteLocalChevalley
import Nyll.EtaleFundamentalGroups.Purity.CompleteLocalSymbolicPowers
import Nyll.EtaleFundamentalGroups.Purity.FinitePowerTorsionLength
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.Push

/-!
# Maximal-ideal saturation of powers

Contracting the maximal-ideal-primary component of a quotient gives the
maximal-ideal saturation of its defining ideal. If an ideal lies in a
nonmaximal prime of a complete Noetherian local domain, its saturated
powers and ordinary powers are cofinal. The finite-length error module
is the maximal-ideal-primary component itself, so no coheight assumption
on the containing prime is required.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

open IsLocalRing

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The maximal-ideal saturation of an ideal, contracted from the torsion
submodule of its quotient. -/
def maximalIdealSaturation (I : Ideal R) : Ideal R :=
  (Ideal.primaryComponent (R ⧸ I) (maximalIdeal R)).comap I.mkQ

/-- Saturation membership is annihilation modulo the ideal by some power
of the maximal ideal. -/
theorem mem_maximalIdealSaturation_iff (I : Ideal R) (x : R) :
    x ∈ maximalIdealSaturation I ↔
      ∃ k : ℕ, ∀ a ∈ maximalIdeal R ^ k, a * x ∈ I := by
  change I.mkQ x ∈ Ideal.primaryComponent (R ⧸ I) (maximalIdeal R) ↔ _
  rw [Ideal.primaryComponent_mem]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun a ha => ?_⟩
    apply (Submodule.Quotient.mk_eq_zero I).mp
    change I.mkQ (a • x) = 0
    rw [map_smul]
    exact (Submodule.mem_torsionBySet_iff (R := R) (M := R ⧸ I)
      (s := ((maximalIdeal R ^ k : Ideal R) : Set R)) (I.mkQ x)).mp hk ⟨a, ha⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero I).mpr (hk a a.property)

/-- Every ideal is contained in its saturation. -/
theorem le_maximalIdealSaturation (I : Ideal R) : I ≤ maximalIdealSaturation I := by
  intro x hx
  exact (mem_maximalIdealSaturation_iff I x).mpr
    ⟨0, fun a _ => I.mul_mem_left a hx⟩

/-- Saturation preserves inclusions of ideals. -/
theorem maximalIdealSaturation_mono : Monotone (maximalIdealSaturation (R := R)) := by
  intro I J hIJ x hx
  obtain ⟨k, hk⟩ := (mem_maximalIdealSaturation_iff I x).mp hx
  exact (mem_maximalIdealSaturation_iff J x).mpr ⟨k, fun a ha => hIJ (hk a ha)⟩

/-- The descending filtration obtained by saturating ordinary powers. -/
def maximalIdealSaturatedPower (I : Ideal R) (n : ℕ) : Ideal R :=
  maximalIdealSaturation (I ^ n)

/-- Ordinary powers are contained in their maximal-ideal saturations. -/
theorem pow_le_maximalIdealSaturatedPower (I : Ideal R) (n : ℕ) :
    I ^ n ≤ maximalIdealSaturatedPower I n :=
  le_maximalIdealSaturation (I ^ n)

/-- Saturated powers form a decreasing filtration. -/
theorem maximalIdealSaturatedPower_antitone (I : Ideal R) :
    Antitone (maximalIdealSaturatedPower I) := by
  intro n m hnm
  exact maximalIdealSaturation_mono (Ideal.pow_le_pow_right hnm)

/-- A saturated power lies in the symbolic power of every containing
nonmaximal prime. -/
theorem maximalIdealSaturatedPower_le_primeSymbolicPower
    (I P : Ideal R) [P.IsPrime] (hIP : I ≤ P)
    (hP : P ≠ maximalIdeal R) (n : ℕ) :
    maximalIdealSaturatedPower I n ≤ primeSymbolicPower P n := by
  obtain ⟨s, hsm, hsp⟩ := IsConcreteLE.exists_of_lt
    (lt_of_le_of_ne (le_maximalIdeal_of_isPrime P) hP)
  intro x hx
  obtain ⟨k, hk⟩ := (mem_maximalIdealSaturation_iff (I ^ n) x).mp hx
  exact (mem_primeSymbolicPower_iff P n x).mpr
    ⟨s ^ k, P.primeCompl.pow_mem hsp k,
      (pow_le_pow_left' hIP n) (hk (s ^ k) (Ideal.pow_mem_pow hsm k))⟩

/-- Saturated powers have zero intersection when the ideal lies in a
nonmaximal prime of a Noetherian local domain. -/
theorem iInf_maximalIdealSaturatedPower_eq_bot
    [IsDomain R] [IsNoetherianRing R]
    (I P : Ideal R) [P.IsPrime] (hIP : I ≤ P)
    (hP : P ≠ maximalIdeal R) :
    (⨅ n : ℕ, maximalIdealSaturatedPower I n) = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← iInf_primeSymbolicPower_eq_bot P]
  exact iInf_mono (maximalIdealSaturatedPower_le_primeSymbolicPower I P hIP hP)

/-- Completeness turns separated saturated powers into an m-adically
cofinal filtration. -/
theorem exists_maximalIdealSaturatedPower_le_maximalIdeal_pow
    [IsDomain R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (I P : Ideal R) [P.IsPrime] (hIP : I ≤ P)
    (hP : P ≠ maximalIdeal R) (k : ℕ) :
    ∃ n : ℕ, maximalIdealSaturatedPower I n ≤ maximalIdeal R ^ k :=
  EtaleFundamentalGroups.exists_le_maximalIdeal_pow_of_antitone_iInf_eq_bot
    (maximalIdealSaturatedPower I) (maximalIdealSaturatedPower_antitone I)
    (iInf_maximalIdealSaturatedPower_eq_bot I P hIP hP) k

/-- The error module introduced by saturation has finite length. -/
theorem isFiniteLength_primaryComponent_quotient
    [IsNoetherianRing R] (I : Ideal R) :
    IsFiniteLength R (Ideal.primaryComponent (R ⧸ I) (maximalIdeal R)) := by
  apply isFiniteLength_of_finite_of_maximalIdealPower_torsion
  intro z
  obtain ⟨k, hk⟩ := (Ideal.primaryComponent_mem
    (M := R ⧸ I) (I := maximalIdeal R) (z : R ⧸ I)).mp z.property
  refine ⟨k, fun a ha => ?_⟩
  apply Subtype.ext
  exact (Submodule.mem_torsionBySet_iff (R := R) (M := R ⧸ I)
    (s := ((maximalIdeal R ^ k : Ideal R) : Set R)) (z : R ⧸ I)).mp hk ⟨a, ha⟩

/-- In a complete Noetherian local domain, saturated powers of an ideal
contained in a nonmaximal prime eventually lie in each ordinary power. -/
theorem exists_maximalIdealSaturatedPower_le_pow_of_le_prime
    [IsDomain R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (I P : Ideal R) [P.IsPrime] (hIP : I ≤ P)
    (hP : P ≠ maximalIdeal R) (n : ℕ) :
    ∃ m : ℕ, maximalIdealSaturatedPower I m ≤ I ^ n := by
  let q : R →ₗ[R] R ⧸ I ^ n := Submodule.mkQ (I ^ n)
  let K : Submodule R (R ⧸ I ^ n) :=
    Ideal.primaryComponent (R ⧸ I ^ n) (maximalIdeal R)
  let : IsArtinian R K := (isFiniteLength_iff_isNoetherian_isArtinian.mp
    (isFiniteLength_primaryComponent_quotient (I ^ n))).2
  let F : ℕ → Submodule R (R ⧸ I ^ n) :=
    fun i => Submodule.map q (maximalIdealSaturatedPower I (n + i))
  have hF (i : ℕ) : F i ≤ K := by
    rintro y ⟨x, hx, rfl⟩
    exact maximalIdealSaturatedPower_antitone I (Nat.le_add_right n i) hx
  let G : ℕ →o (Submodule R K)ᵒᵈ :=
    { toFun := fun i => (F i).comap K.subtype
      monotone' := fun _ _ hij =>
        Submodule.comap_mono (Submodule.map_mono
          (maximalIdealSaturatedPower_antitone I (Nat.add_le_add_left hij n))) }
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes G
  refine ⟨n + N, ?_⟩
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero (I ^ n)).mp
  have hxF : q x ∈ F N := Submodule.mem_map_of_mem (f := q) hx
  let y : K := ⟨q x, hF N hxF⟩
  have hy : y ∈ (G N).ofDual := hxF
  change q x = 0
  apply IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal R) (R ⧸ I ^ n))
  intro k
  apply SModEq.zero.mpr
  obtain ⟨m, hm⟩ := exists_maximalIdealSaturatedPower_le_maximalIdeal_pow I P hIP hP k
  have hy' : y ∈ (G (max N m)).ofDual :=
    (hN (max N m) (le_max_left N m)) ▸ hy
  have hxF' : q x ∈ F (max N m) := hy'
  have hsmall : maximalIdealSaturatedPower I (n + max N m) ≤ maximalIdeal R ^ k :=
    (maximalIdealSaturatedPower_antitone I
      ((le_max_right N m).trans (Nat.le_add_left (max N m) n))).trans hm
  have hxmap : q x ∈ Submodule.map q (maximalIdeal R ^ k) :=
    Submodule.map_mono hsmall hxF'
  obtain ⟨a, ha, heq⟩ := Submodule.mem_map.mp hxmap
  have ha' : a ∈ ((maximalIdeal R ^ k) • ⊤ : Submodule R R) := by
    simpa only [Ideal.smul_eq_mul, ← Ideal.one_eq_top, mul_one] using ha
  have hmap := Submodule.mem_map_of_mem (f := q) ha'
  rw [Submodule.map_smul'', Submodule.map_top] at hmap
  rw [Submodule.range_mkQ] at hmap
  rw [heq] at hmap
  exact hmap

/-- A proper ideal whose radical is not the maximal ideal is contained
in a nonmaximal prime. -/
theorem exists_nonmaximal_prime_over_of_radical_ne
    (I : Ideal R) (hI : I ≠ ⊤) (hrad : I.radical ≠ maximalIdeal R) :
    ∃ P : Ideal R, I ≤ P ∧ P.IsPrime ∧ P ≠ maximalIdeal R := by
  classical
  by_contra h
  push Not at h
  apply hrad
  apply le_antisymm
  · exact (maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr (le_maximalIdeal hI)
  · rw [I.radical_eq_sInf]
    apply le_sInf
    intro P hP
    rw [h P hP.1 hP.2]

/-- Saturation does not change the adic topology of a proper ideal whose
radical is not the maximal ideal in a complete Noetherian local domain. -/
theorem exists_maximalIdealSaturatedPower_le_pow
    [IsDomain R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≠ ⊤) (hrad : I.radical ≠ maximalIdeal R) (n : ℕ) :
    ∃ m : ℕ, maximalIdealSaturatedPower I m ≤ I ^ n := by
  obtain ⟨P, hIP, hprime, hP⟩ := exists_nonmaximal_prime_over_of_radical_ne I hI hrad
  let : P.IsPrime := hprime
  exact exists_maximalIdealSaturatedPower_le_pow_of_le_prime I P hIP hP n

end EtaleFundamentalGroups.Purity

end
