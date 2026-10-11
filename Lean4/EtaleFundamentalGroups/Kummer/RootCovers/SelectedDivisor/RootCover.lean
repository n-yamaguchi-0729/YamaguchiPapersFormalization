/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedRegularity
import EtaleFundamentalGroups.Kummer.IteratedRadical.BaseChange
import EtaleFundamentalGroups.Kummer.Obstructions.LocalDerivative
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# A selected divisor under a one-root Kummer cover

Let `[x, y]` be a regular parameter pair generating the maximal ideal of a
Noetherian local domain.  After adjoining a positive-degree root of `x`, this
file proves that the cover is a regular local domain, that the image of `y`
remains prime, and that its quotient is again both a domain and a regular
local ring.

The proof does not assume primality of `y`.  It first produces the domain
structure on `R ⧸ (y)` from regularity of the residual parameter `x`; the
cover quotient is then identified with the corresponding base-changed root
cover.  Finally, faithful flatness preserves regularity of `y`, and Krull
intersection upgrades the regular local cover to a domain.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped Pointwise
open Polynomial
open IsLocalRing
open RingTheory.Sequence

universe u

/-- Modding out the second member of a regular parameter pair leaves the first
member regular and generating the quotient maximal ideal. -/
theorem regular_quotient_parameter_of_regular_pair
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let I : Ideal R := Ideal.span {y}
    let S := R ⧸ I
    IsRegular S [Ideal.Quotient.mk I x] ∧
      Ideal.ofList [Ideal.Quotient.mk I x] =
        (maximalIdeal R).map (Ideal.Quotient.mk I) := by
  dsimp only
  let I : Ideal R := Ideal.span {y}
  let S := R ⧸ I
  have hyMem : y ∈ maximalIdeal R := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  have hIle : I ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    change y ∈ maximalIdeal R
    exact hyMem
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hregYX : IsRegular R [y, x] :=
    IsLocalRing.isRegular_of_perm hreg (List.Perm.swap x y []).symm
  have hspan_smul : y • (⊤ : Submodule R R) = (I : Submodule R R) := by
    rw [← Submodule.ideal_span_singleton_smul]
    change I • (⊤ : Submodule R R) = (I : Submodule R R)
    simp
  have hxregQ : IsSMulRegular (QuotSMulTop y R) x :=
    ((isRegular_cons_iff (QuotSMulTop y R) x []).mp
      ((isRegular_cons_iff R y [x]).mp hregYX).2).1
  have hxregS : IsSMulRegular S (Ideal.Quotient.mk I x) := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro z hz
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hxmemI : x * r ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul, smul_eq_mul] using hz
    have hxmem : x • r ∈ y • (⊤ : Submodule R R) := by
      rw [hspan_smul]
      simpa only [smul_eq_mul] using hxmemI
    have hrmem : r ∈ y • (⊤ : Submodule R R) :=
      (isSMulRegular_quotient_iff_mem_of_smul_mem
        (y • (⊤ : Submodule R R)) x).mp hxregQ r hxmem
    rw [hspan_smul] at hrmem
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hrmem
  have hregS : IsRegular S [Ideal.Quotient.mk I x] := by
    have hxmem : Ideal.Quotient.mk I x ∈ maximalIdeal S := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
        ← hgen, Ideal.map_ofList]
      apply Ideal.subset_span
      simp only [List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl rfl
    exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
      (L := S) (by
        intro z hz
        simp only [List.mem_singleton] at hz
        subst z
        exact hxmem)
      ((isWeaklyRegular_singleton_iff S (Ideal.Quotient.mk I x)).mpr hxregS)
  have hgenS : Ideal.ofList [Ideal.Quotient.mk I x] =
      (maximalIdeal R).map (Ideal.Quotient.mk I) := by
    rw [← hgen, Ideal.map_ofList]
    simp [I]
  exact ⟨hregS, hgenS⟩

private theorem isDomain_of_prime_regular_element
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {p : R} (hp : Prime p) (hpreg : IsSMulRegular R p) : IsDomain R := by
  have hbot : (⊥ : Ideal R).IsPrime := by
    rw [Ideal.isPrime_iff]
    refine ⟨bot_ne_top, ?_⟩
    intro a b hab
    simp only [Ideal.mem_bot] at hab ⊢
    by_contra hzero
    push Not at hzero
    obtain ⟨k, hak⟩ : ∃ k : ℕ, a ∉ maximalIdeal R ^ k := by
      by_contra hall
      push Not at hall
      have haInf : a ∈ ⨅ k : ℕ, maximalIdeal R ^ k := Ideal.mem_iInf.mpr hall
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing
        (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top] at haInf
      exact hzero.1 (Ideal.mem_bot.mp haInf)
    obtain ⟨l, hbl⟩ : ∃ l : ℕ, b ∉ maximalIdeal R ^ l := by
      by_contra hall
      push Not at hall
      have hbInf : b ∈ ⨅ l : ℕ, maximalIdeal R ^ l := Ideal.mem_iInf.mpr hall
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing
        (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top] at hbInf
      exact hzero.2 (Ideal.mem_bot.mp hbInf)
    have hpMem : p ∈ maximalIdeal R := by
      rw [mem_maximalIdeal]
      exact hp.not_isUnit
    have hpow : ∀ k l : ℕ, ∀ a b : R, a * b = 0 →
        p ^ k ∣ a ∨ p ^ l ∣ b := by
      intro k
      induction k with
      | zero =>
          intro l a b hab
          exact Or.inl (by simp)
      | succ k ihK =>
          intro l
          induction l with
          | zero =>
              intro a b hab
              exact Or.inr (by simp)
          | succ l ihL =>
              intro a b hab
              have hpProd : p ∣ a * b := by rw [hab]; exact dvd_zero p
              rcases hp.dvd_mul.mp hpProd with hpa | hpb
              · obtain ⟨a', rfl⟩ := hpa
                have hab' : a' * b = 0 := by
                  apply hpreg.right_eq_zero_of_smul
                  simpa only [smul_eq_mul, mul_assoc] using hab
                rcases ihK (l + 1) a' b hab' with ha' | hb'
                · left
                  obtain ⟨c, hc⟩ := ha'
                  refine ⟨c, ?_⟩
                  rw [hc, pow_succ]
                  ac_rfl
                · exact Or.inr hb'
              · obtain ⟨b', rfl⟩ := hpb
                have hab' : a * b' = 0 := by
                  apply hpreg.right_eq_zero_of_smul
                  simpa only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hab
                rcases ihL a b' hab' with ha' | hb'
                · exact Or.inl ha'
                · right
                  obtain ⟨c, hc⟩ := hb'
                  refine ⟨c, ?_⟩
                  rw [hc, pow_succ]
                  ac_rfl
    rcases hpow k l a b hab with ha | hb
    · apply hak
      obtain ⟨c, rfl⟩ := ha
      exact (maximalIdeal R ^ k).mul_mem_right c
        (Ideal.pow_mem_pow hpMem k)
    · apply hbl
      obtain ⟨c, rfl⟩ := hb
      exact (maximalIdeal R ^ l).mul_mem_right c
        (Ideal.pow_mem_pow hpMem l)
  let : (⊥ : Ideal R).IsPrime := hbot
  exact IsDomain.of_bot_isPrime R

/--
After adjoining an `n`th root of the first member of a regular parameter pair,
the second member remains a prime regular divisor.  The root cover and the
quotient by that selected divisor are regular local domains.
-/
theorem oneRootCover_selectedDivisor_geometry
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    {n : ℕ} (hn : 0 < n) {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let n₁ : Fin 1 → ℕ := fun _ ↦ n
    let a₁ : Fin 1 → R := fun _ ↦ x
    let B := iteratedRadical R 1 n₁ a₁
    IsRegularLocalRing B ∧ IsDomain B ∧
      Prime (algebraMap R B y) ∧
      IsDomain (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) ∧
      IsRegularLocalRing
        (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) := by
  dsimp only
  let n₁ : Fin 1 → ℕ := fun _ ↦ n
  let a₁ : Fin 1 → R := fun _ ↦ x
  let B := iteratedRadical R 1 n₁ a₁
  have hn₁ : ∀ i, 0 < n₁ i := fun _ ↦ hn
  have hxMem : x ∈ maximalIdeal R := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  have ha₁Mem : ∀ i, a₁ i ∈ maximalIdeal R := fun _ ↦ hxMem
  let : IsLocalRing B := isLocalRing_iteratedRadical n₁ a₁ hn₁ ha₁Mem
  have hregB : IsRegularLocalRing B := by
    apply isRegularLocalRing_iteratedRadical_of_regular_parameters
      n₁ a₁ [y] hn₁
    · simpa [a₁] using hreg
    · simpa [a₁] using hgen
  let : IsRegularLocalRing B := hregB
  let : Module.Finite R B := finite_iteratedRadical n₁ a₁ hn₁
  let : Module.FaithfullyFlat R B :=
    faithfullyFlat_iteratedRadical n₁ a₁ hn₁
  let I : Ideal R := Ideal.span {y}
  have hyMem : y ∈ maximalIdeal R := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  have hIle : I ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    change y ∈ maximalIdeal R
    exact hyMem
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R (R ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hS := regular_quotient_parameter_of_regular_pair hreg hgen
  have hregS : IsRegular (R ⧸ I) [algebraMap R (R ⧸ I) x] := by
    simpa [I, Ideal.Quotient.algebraMap_eq] using hS.1
  have hgenS : Ideal.ofList [algebraMap R (R ⧸ I) x] =
      maximalIdeal (R ⧸ I) := by
    calc
      Ideal.ofList [algebraMap R (R ⧸ I) x] =
          (maximalIdeal R).map (Ideal.Quotient.mk I) := by
        simpa [I, Ideal.Quotient.algebraMap_eq] using hS.2
      _ = maximalIdeal (R ⧸ I) :=
        IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hxSNe : algebraMap R (R ⧸ I) x ≠ 0 := by
    have hxreg : IsSMulRegular (R ⧸ I) (algebraMap R (R ⧸ I) x) :=
      ((isRegular_cons_iff (R ⧸ I) (algebraMap R (R ⧸ I) x) []).mp hregS).1
    intro hx
    have hxzero : algebraMap R (R ⧸ I) x • (1 : R ⧸ I) = 0 := by
      rw [hx]
      exact zero_smul (R ⧸ I) 1
    have hone : (1 : R ⧸ I) = 0 := hxreg.right_eq_zero_of_smul hxzero
    exact one_ne_zero hone
  have hspanS : Ideal.span ({algebraMap R (R ⧸ I) x} : Set (R ⧸ I)) =
      maximalIdeal (R ⧸ I) := by
    simpa using hgenS
  have hxSPrime : Prime (algebraMap R (R ⧸ I) x) := by
    apply (Ideal.span_singleton_prime hxSNe).mp
    rw [hspanS]
    exact inferInstance
  have hdomainS : IsDomain (R ⧸ I) :=
    isDomain_of_prime_regular_element hxSPrime
      (((isRegular_cons_iff (R ⧸ I)
        (algebraMap R (R ⧸ I) x) []).mp hregS).1)
  let : IsDomain (R ⧸ I) := hdomainS
  have hmaxPrincipal : (maximalIdeal (R ⧸ I)).IsPrincipal :=
    ⟨algebraMap R (R ⧸ I) x, hspanS.symm⟩
  let : IsPrincipalIdealRing (R ⧸ I) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R ⧸ I)).out 5 1).mp
      hmaxPrincipal
  let D := iteratedRadical (R ⧸ I) 1 n₁
    (fun i ↦ algebraMap R (R ⧸ I) (a₁ i))
  have hregD : IsRegularLocalRing D := by
    apply isRegularLocalRing_iteratedRadical_of_regular_parameters
      n₁ (fun i ↦ algebraMap R (R ⧸ I) (a₁ i)) [] hn₁
    · simpa [a₁] using hregS
    · simpa [a₁] using hgenS
  let : IsRegularLocalRing D := hregD
  have hdomainD : IsDomain D := by
    let q : (R ⧸ I)[X] :=
      X ^ n - Polynomial.C (Ideal.Quotient.mk I x)
    have hqPrime : Prime q := by
      exact (irreducible_X_pow_sub_C_of_prime
        (by simpa [Ideal.Quotient.algebraMap_eq] using hxSPrime) hn).prime
    have hcoeff :
        algebraMap (R ⧸ I)
            (iteratedRadical (R ⧸ I) 0 (Fin.init n₁)
              (Fin.init fun i ↦ algebraMap R (R ⧸ I) (a₁ i)))
            (algebraMap R (R ⧸ I) (a₁ (Fin.last 0))) =
          Ideal.Quotient.mk I x := by
      change algebraMap (R ⧸ I) (R ⧸ I) (Ideal.Quotient.mk I x) =
        Ideal.Quotient.mk I x
      exact Algebra.algebraMap_self_apply _
    let qD : (R ⧸ I)[X] :=
      X ^ n₁ (Fin.last 0) -
        Polynomial.C
          (algebraMap (R ⧸ I)
            (iteratedRadical (R ⧸ I) 0 (Fin.init n₁)
              (Fin.init fun i ↦ algebraMap R (R ⧸ I) (a₁ i)))
            (algebraMap R (R ⧸ I) (a₁ (Fin.last 0))))
    have hqD : qD = q := by
      dsimp only [qD]
      rw [hcoeff]
      simp [q, n₁]
      rfl
    let eqv : D ≃ₐ[R ⧸ I] AdjoinRoot q :=
      AdjoinRoot.algEquivOfEq (R ⧸ I) qD q hqD
    let : IsDomain (AdjoinRoot q) := AdjoinRoot.isDomain_of_prime hqPrime
    exact eqv.toMulEquiv.isDomain (AdjoinRoot q)
  let : IsDomain D := hdomainD
  let J : Ideal B := I.map (algebraMap R B)
  let e : (B ⧸ J) ≃ₐ[R ⧸ I] D :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).trans
      (iteratedRadicalBaseChangeAlgEquiv n₁ a₁)
  have hdomainBJ : IsDomain (B ⧸ J) := e.toMulEquiv.isDomain D
  let : IsDomain (B ⧸ J) := hdomainBJ
  have hJprime : J.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime J).mp inferInstance
  have hJspan : J = Ideal.span ({algebraMap R B y} : Set B) := by
    simp [J, I, Ideal.map_span]
  have hregYX : IsRegular R [y, x] :=
    IsLocalRing.isRegular_of_perm hreg (List.Perm.swap x y []).symm
  have hyregR : IsSMulRegular R y :=
    ((isRegular_cons_iff R y [x]).mp hregYX).1
  have hyNe : y ≠ 0 := by
    intro hyzero
    have hone : (1 : R) = 0 := by
      apply hyregR.right_eq_zero_of_smul
      simp only [hyzero, zero_smul]
    exact one_ne_zero hone
  have hyBNe : algebraMap R B y ≠ 0 := by
    intro hzero
    apply hyNe
    apply FaithfulSMul.algebraMap_injective R B
    simpa using hzero
  have hyBPrime : Prime (algebraMap R B y) := by
    apply (Ideal.span_singleton_prime hyBNe).mp
    rw [← hJspan]
    exact hJprime
  have hyregTensor : @IsSMulRegular R (TensorProduct R (↑B) R) _ y :=
    hyregR.lTensor B
  have hyregBR : @IsSMulRegular R (↑B) _ y :=
    ((TensorProduct.rid R B).isSMulRegular_congr y).mp hyregTensor
  have hyregB : @IsSMulRegular (↑B) (↑B) _ (algebraMap R B y) := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro z hz
    apply hyregBR.right_eq_zero_of_smul
    simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply] using hz
  have hdomainB : IsDomain B :=
    isDomain_of_prime_regular_element (R := B)
      (p := algebraMap R B y) hyBPrime hyregB
  have hregBJ : IsRegularLocalRing (B ⧸ J) :=
    IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  have hdomainBspan : IsDomain
      (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) := by
    rw [← hJspan]
    exact hdomainBJ
  have hregBspan : IsRegularLocalRing
      (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) := by
    rw [← hJspan]
    exact hregBJ
  exact ⟨hregB, hdomainB, hyBPrime, hdomainBspan, hregBspan⟩

end EtaleFundamentalGroups.Kummer

end
