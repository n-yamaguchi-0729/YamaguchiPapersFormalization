/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Finiteness.Ideal
import EtaleFundamentalGroups.FiniteEtale.HenselianAscent
import EtaleFundamentalGroups.Kummer.RootCovers.Local.Residue
import SchemeTheory.FiniteEtale.Henselian.ChosenFactor.Core
import ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite

/-!
# Complete local iterated root covers

A finite iterated positive root cover of closed-point elements is complete for
its own maximal ideal when the Noetherian local base is complete.  Finite-module
completeness first gives completeness for the extended base maximal ideal.  The
two adic filtrations are then compared using integrality and localness: the
upstairs maximal ideal is the radical of the extended ideal, so a positive
power lies in that extended ideal.

All algebraic and local structures are installed only inside the proofs.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u

open ValuationTheory.DiscreteValuationField
open Polynomial

/-- Finite generation of the closed point is preserved by a positive
iterated root cover.

At each stage the new maximal ideal is the image of the preceding maximal
ideal together with the single adjoined root.  This explicit producer avoids
installing a Noetherian-ring instance merely to compare the two adic
filtrations. -/
theorem maximalIdeal_fg_iteratedRadical
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    (IsLocalRing.maximalIdeal B).FG := by
  induction r with
  | zero =>
      change (IsLocalRing.maximalIdeal A).FG
      exact hmax
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      let : IsLocalRing T :=
        isLocalRing_iteratedRadical
          (Fin.init n) (Fin.init a)
          (fun i ↦ hn i.castSucc) (fun i ↦ ha i.castSucc)
      have hmaxT : (IsLocalRing.maximalIdeal T).FG :=
        ih (Fin.init n) (Fin.init a)
          (fun i ↦ hn i.castSucc) (fun i ↦ ha i.castSucc)
      have haLast :
          algebraMap A T (a (Fin.last r)) ∈ IsLocalRing.maximalIdeal T :=
        algebraMap_mem_maximalIdeal_iteratedRadical
          (Fin.init n) (Fin.init a)
          (fun i ↦ hn i.castSucc) (fun i ↦ ha i.castSucc)
          (ha (Fin.last r))
      let : IsLocalRing (AdjoinRoot f) :=
        isLocalRing_adjoinRoot_X_pow_sub_C (hn (Fin.last r)) haLast
      change (IsLocalRing.maximalIdeal (AdjoinRoot f)).FG
      rw [maximalIdeal_adjoinRoot_X_pow_sub_C
        (hn (Fin.last r)) haLast]
      exact Submodule.FG.sup
        (hmaxT.map (AdjoinRoot.of f))
        (Submodule.fg_span (Set.finite_singleton (AdjoinRoot.root f)))

/-- A finite positive iterated root cover of closed-point elements is
complete for its own maximal ideal as soon as the base is complete and its
maximal ideal is finitely generated.

No Noetherian-ring instance is required.  Freeness transfers completeness
to the extended base ideal, while the explicit finite generation theorem
above makes the two adic filtrations cofinal. -/
theorem isAdicComplete_maximalIdeal_iteratedRadical_of_fg
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  dsimp only
  let B := iteratedRadical A r n a
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Module.Free A B := free_iteratedRadical n a hn
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let I : Ideal B :=
    (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  let J : Ideal B := IsLocalRing.maximalIdeal B
  have hcompleteBase :
      IsAdicComplete (IsLocalRing.maximalIdeal A) B :=
    isAdicComplete_of_moduleFinite_of_moduleFree
      (I := IsLocalRing.maximalIdeal A) (M := B)
  let : IsAdicComplete I B :=
    (isAdicComplete_map_algebraMap_iff
      (R := A) (S := B) (IsLocalRing.maximalIdeal A)).2 hcompleteBase
  have hIJ : I ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact algebraMap_mem_maximalIdeal_iteratedRadical n a hn ha hx
  have hJradical : J ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP ↦ ?_
    rcases hP with ⟨hIP, hPprime⟩
    let : P.IsPrime := hPprime
    have hbase_le : IsLocalRing.maximalIdeal A ≤
        P.comap (algebraMap A B) :=
      (Ideal.map_le_iff_le_comap).1 hIP
    have hcomap_ne_top : P.comap (algebraMap A B) ≠ ⊤ :=
      (show (P.comap (algebraMap A B)).IsPrime from inferInstance).ne_top
    have hcomap_eq : IsLocalRing.maximalIdeal A =
        P.comap (algebraMap A B) :=
      (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
        hcomap_ne_top hbase_le
    have hcomap_maximal :
        (P.comap (algebraMap A B)).IsMaximal := by
      rw [← hcomap_eq]
      exact IsLocalRing.maximalIdeal.isMaximal A
    have hPmaximal : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under
        (R := A) (S := B) P hcomap_maximal
    have hP_eq : P = J := IsLocalRing.eq_maximalIdeal hPmaximal
    rw [hP_eq]
  have hJfg : J.FG :=
    maximalIdeal_fg_iteratedRadical hmax n a hn ha
  obtain ⟨k, hk⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hJradical hJfg
  have hk' : J ^ (k + 1) ≤ I :=
    (Ideal.pow_le_pow_right (Nat.le_add_right k 1)).trans hk
  exact isAdicComplete_of_le_of_pow_le
    I J (Nat.zero_lt_succ k) hIJ (by simpa [Nat.succ_eq_add_one] using hk')

/-- A finite positive iterated root cover of closed-point elements over a
Noetherian adically complete local ring is complete for its own maximal
ideal. -/
theorem isAdicComplete_maximalIdeal_iteratedRadical
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  exact isAdicComplete_maximalIdeal_iteratedRadical_of_fg
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing n a hn ha

/-- Henselianity of an iterated root cover over a complete local base with
finitely generated maximal ideal.  This is the Noetherian-free form used
after passing to an adic completion. -/
theorem henselianLocalRing_iteratedRadical_of_isAdicComplete_of_fg
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    HenselianLocalRing B := by
  dsimp only
  let B := iteratedRadical A r n a
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
    isAdicComplete_maximalIdeal_iteratedRadical_of_fg hmax n a hn ha
  let : HenselianRing B (IsLocalRing.maximalIdeal B) := inferInstance
  refine
    { is_henselian := ?_ }
  intro f hf x hx hderivative
  exact HenselianRing.is_henselian f hf x hx
    (hderivative.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)))

/-- A finite positive iterated root cover of closed-point elements over a
Noetherian complete local ring is Henselian local. -/
theorem henselianLocalRing_iteratedRadical_of_isAdicComplete
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    HenselianLocalRing B := by
  exact henselianLocalRing_iteratedRadical_of_isAdicComplete_of_fg
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing n a hn ha

/-- The unique finite étale chosen factor over an iterated root cover of a
complete local ring with finitely generated maximal ideal is trivial when
the base residue field is separably closed. -/
theorem algebraMap_bijective_of_unique_prime_over_iteratedRadical_of_fg
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    ∀ {S : Type u} [CommRing S] [Algebra B S]
      [Module.Finite B S] [Algebra.Etale B S],
      ∀ (q : Ideal S) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        (∀ Q : Ideal S, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q) →
        Function.Bijective (algebraMap B S) := by
  dsimp only
  intro S _ _ _ _ q _ _ hunique
  let B := iteratedRadical A r n a
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : HenselianLocalRing B :=
    henselianLocalRing_iteratedRadical_of_isAdicComplete_of_fg
      hmax n a hn ha
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a hn
  let : IsSepClosed (IsLocalRing.ResidueField B) :=
    isSepClosed_residueField_iteratedRadical n a hn ha
  exact
    algebraMap_bijective_of_unique_prime_over_maximal_of_strictHenselian
      q hunique

/-- Over a Noetherian complete local base with separably closed residue field,
the unique chosen finite étale factor above the closed point of an iterated
positive root cover is the root cover itself.  The Henselian and residue-field
hypotheses required by the strict-Henselian splitting theorem are both
produced internally. -/
theorem algebraMap_bijective_of_unique_prime_over_iteratedRadical
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    ∀ {S : Type u} [CommRing S] [Algebra B S]
      [Module.Finite B S] [Algebra.Etale B S],
      ∀ (q : Ideal S) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        (∀ Q : Ideal S, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q) →
        Function.Bijective (algebraMap B S) := by
  exact algebraMap_bijective_of_unique_prime_over_iteratedRadical_of_fg
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing n a hn ha

end EtaleFundamentalGroups.Kummer

end
