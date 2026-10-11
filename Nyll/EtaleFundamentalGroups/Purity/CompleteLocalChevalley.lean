/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Descending ideals in complete local rings

Chevalley's lemma compares a descending sequence of ideals with zero
intersection to the powers of the maximal ideal.  The proof uses stable
images modulo these powers and lifts compatible representatives directly.
-/

noncomputable section

open IsLocalRing

namespace EtaleFundamentalGroups

universe u

variable {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]

private theorem maximalIdeal_pow_quotient_artinian (k : ℕ) :
    IsArtinianRing (C ⧸ maximalIdeal C ^ k) := by
  cases k with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
  | succ k =>
      apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
      rw [← Ideal.radical_minimalPrimes,
        (maximalIdeal C).radical_pow (Nat.succ_ne_zero k),
        (maximalIdeal.isMaximal C).isPrime.isRadical.radical,
        Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton (maximalIdeal C)

/-- The images of a descending sequence of ideals modulo a fixed power of
the maximal ideal stabilize. -/
theorem exists_eq_iInf_sup_maximalIdeal_pow
    (J : ℕ → Ideal C) (hJ : Antitone J) (k : ℕ) :
    ∃ N : ℕ, J N ⊔ maximalIdeal C ^ k =
      ⨅ n : ℕ, J n ⊔ maximalIdeal C ^ k := by
  let : IsArtinianRing (C ⧸ maximalIdeal C ^ k) :=
    maximalIdeal_pow_quotient_artinian k
  let q : C →+* C ⧸ maximalIdeal C ^ k :=
    Ideal.Quotient.mk (maximalIdeal C ^ k)
  let f : ℕ →o (Ideal (C ⧸ maximalIdeal C ^ k))ᵒᵈ :=
    { toFun := fun n => (J n).map q
      monotone' := fun _ _ h => Ideal.map_mono (hJ h) }
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes f
  have hstable (n : ℕ) (hn : N ≤ n) :
      J N ⊔ maximalIdeal C ^ k = J n ⊔ maximalIdeal C ^ k := by
    have heq : (J N).map q = (J n).map q := hN n hn
    have hcomap := congrArg (Ideal.comap q) heq
    simpa only [q, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hcomap
  refine ⟨N, le_antisymm (le_iInf fun n => ?_) (iInf_le _ N)⟩
  calc
    J N ⊔ maximalIdeal C ^ k = J (max N n) ⊔ maximalIdeal C ^ k :=
      hstable (max N n) (le_max_left N n)
    _ ≤ J n ⊔ maximalIdeal C ^ k :=
      sup_le_sup_right (hJ (le_max_right N n)) _

/-- Every ideal of a Noetherian local ring is closed for the topology
defined by powers of the maximal ideal. -/
theorem mem_ideal_of_mem_sup_maximalIdeal_pow
    (J : Ideal C) (x : C)
    (hx : ∀ n : ℕ, x ∈ J ⊔ maximalIdeal C ^ n) : x ∈ J := by
  have hzero : Submodule.mkQ J x = 0 := by
    apply IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal C) (C ⧸ J))
    intro n
    apply SModEq.zero.mpr
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hx n)
    have hb' : b ∈ ((maximalIdeal C ^ n) • ⊤ : Submodule C C) := by
      simpa only [Ideal.smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hb
    have hmap := Submodule.mem_map_of_mem (f := Submodule.mkQ J) hb'
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hmap
    have ha0 : Submodule.mkQ J a = 0 := (Submodule.Quotient.mk_eq_zero J).mpr ha
    rw [← hab, map_add, ha0, zero_add]
    exact hmap
  exact (Submodule.Quotient.mk_eq_zero J).mp hzero

/-- **Chevalley's lemma**: in a complete Noetherian local ring, every
descending sequence of ideals with zero intersection is eventually contained
in each power of the maximal ideal. -/
theorem exists_le_maximalIdeal_pow_of_antitone_iInf_eq_bot
    [IsAdicComplete (maximalIdeal C) C]
    (J : ℕ → Ideal C) (hJ : Antitone J)
    (hinf : (⨅ n : ℕ, J n) = ⊥) (k : ℕ) :
    ∃ N : ℕ, J N ≤ maximalIdeal C ^ k := by
  let L : ℕ → Ideal C := fun n => ⨅ r : ℕ, J r ⊔ maximalIdeal C ^ n
  have hstep (n : ℕ) (x : C) (hx : x ∈ L n) :
      ∃ y : C, y ∈ L (n + 1) ∧ x - y ∈ maximalIdeal C ^ n := by
    obtain ⟨N, hN⟩ := exists_eq_iInf_sup_maximalIdeal_pow J hJ (n + 1)
    have hxN : x ∈ J N ⊔ maximalIdeal C ^ n := (Submodule.mem_iInf _).mp hx N
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxN
    refine ⟨a, ?_, ?_⟩
    · change a ∈ ⨅ r : ℕ, J r ⊔ maximalIdeal C ^ (n + 1)
      rw [← hN]
      exact (show J N ≤ J N ⊔ maximalIdeal C ^ (n + 1) from le_sup_left) ha
    · rw [← hab, add_sub_cancel_left]
      exact hb
  have hL (x : C) (hx : x ∈ L k) : x ∈ maximalIdeal C ^ k := by
    let a : (n : ℕ) → L (k + n) :=
      Nat.rec (motive := fun n => L (k + n))
        ⟨x, by simpa only [Nat.add_zero] using hx⟩
        (fun n y =>
          let h := hstep (k + n) y.1 y.2
          ⟨h.choose, by simpa only [Nat.add_assoc] using h.choose_spec.1⟩)
    have ha0 : (a 0).1 = x := by rfl
    have haStep (n : ℕ) :
        (a n).1 - (a (n + 1)).1 ∈ maximalIdeal C ^ (k + n) := by
      change (a n).1 - (hstep (k + n) (a n).1 (a n).2).choose ∈
        maximalIdeal C ^ (k + n)
      exact (hstep (k + n) (a n).1 (a n).2).choose_spec.2
    have haPair (i j : ℕ) (hij : i ≤ j) :
        (a i).1 - (a j).1 ∈ maximalIdeal C ^ (k + i) := by
      induction j, hij using Nat.le_induction with
      | base =>
          rw [sub_self]
          exact (maximalIdeal C ^ (k + i)).zero_mem
      | succ j hij ih =>
          have hstep' : (a j).1 - (a (j + 1)).1 ∈
              maximalIdeal C ^ (k + i) :=
            Ideal.pow_le_pow_right (Nat.add_le_add_left hij k) (haStep j)
          have hsum := (maximalIdeal C ^ (k + i)).add_mem ih hstep'
          simpa only [sub_add_sub_cancel] using hsum
    have hcauchy {i j : ℕ} (hij : i ≤ j) :
        (a i).1 ≡ (a j).1
          [SMOD ((maximalIdeal C ^ i) • ⊤ : Submodule C C)] := by
      apply SModEq.sub_mem.mpr
      have hdiff : (a i).1 - (a j).1 ∈ maximalIdeal C ^ i :=
        Ideal.pow_le_pow_right (Nat.le_add_left i k) (haPair i j hij)
      simpa only [Ideal.smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hdiff
    obtain ⟨z, hz⟩ := IsPrecomplete.prec
      (inferInstance : IsPrecomplete (maximalIdeal C) C)
      (f := fun n => (a n).1) hcauchy
    have hzJ (r : ℕ) : z ∈ J r := by
      apply mem_ideal_of_mem_sup_maximalIdeal_pow (J r) z
      intro n
      have haIn : (a n).1 ∈ J r ⊔ maximalIdeal C ^ (k + n) :=
        (Submodule.mem_iInf _).mp (a n).2 r
      have haIn' : (a n).1 ∈ J r ⊔ maximalIdeal C ^ n :=
        (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_add_left n k)) (J r)) haIn
      have hdiff : z - (a n).1 ∈ maximalIdeal C ^ n := by
        have hdiff' := SModEq.sub_mem.mp (hz n).symm
        simpa only [Ideal.smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hdiff'
      have hdiffSup : z - (a n).1 ∈ J r ⊔ maximalIdeal C ^ n :=
        (le_sup_right : maximalIdeal C ^ n ≤ J r ⊔ maximalIdeal C ^ n) hdiff
      have hsum := (J r ⊔ maximalIdeal C ^ n).add_mem hdiffSup haIn'
      simpa only [sub_add_cancel] using hsum
    have hz0 : z = 0 := by
      have hzinf : z ∈ ⨅ r : ℕ, J r := (Submodule.mem_iInf J).mpr hzJ
      simpa only [hinf, Submodule.mem_bot] using hzinf
    have hfirst : x - (a k).1 ∈ maximalIdeal C ^ k := by
      simpa only [ha0, Nat.add_zero] using haPair 0 k (Nat.zero_le k)
    have hlast : (a k).1 - z ∈ maximalIdeal C ^ k := by
      have hlast' := SModEq.sub_mem.mp (hz k)
      simpa only [Ideal.smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hlast'
    have hsum := (maximalIdeal C ^ k).add_mem hfirst hlast
    simpa only [sub_add_sub_cancel, hz0, sub_zero, sub_add_cancel] using hsum
  obtain ⟨N, hN⟩ := exists_eq_iInf_sup_maximalIdeal_pow J hJ k
  refine ⟨N, ?_⟩
  intro x hx
  apply hL x
  change x ∈ ⨅ n : ℕ, J n ⊔ maximalIdeal C ^ k
  rw [← hN]
  exact (show J N ≤ J N ⊔ maximalIdeal C ^ k from le_sup_left) hx

end EtaleFundamentalGroups

end
