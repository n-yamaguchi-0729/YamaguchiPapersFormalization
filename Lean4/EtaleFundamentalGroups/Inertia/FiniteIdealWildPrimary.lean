/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.IntegralAutomorphismLocalizedWildOrder
import EtaleFundamentalGroups.Inertia.FiniteIdealTameOrder
import ValuedFieldTheory.Ramification.HilbertRamification.RingPrincipalInertiaCriterion
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Ring.Aut
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Primary wild orders at finite ideals

Proves that the principal-unit wild order of the original normalization action is a power of the
residue exponential characteristic.
-/

noncomputable section

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

/-- The order of the same actual principal-unit subgroup of the original
normalization-prime action is a power of its own residue exponential
characteristic. The intrinsic automorphism order law is constructed before
forgetting the coefficient algebra, then applied to the actual subgroup. -/
theorem finiteIdealWildOrder_exists_expChar_pow
    (A : Type u) (B : Type v)
    [rA : CommRing A] [dA : IsDomain A]
    [rB : CommRing B] [dB : IsDedekindDomain B]
    [aAB : Algebra A B] [finAB : Module.Finite A B] [tfAB : Module.IsTorsionFree A B] :
    ∀ (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥),
      ∃ n : ℕ, finiteIdealWildOrder B (B ≃ₐ[A] B) Q hQ =
        (ringExpChar Q.ResidueField) ^ n := by
  let G := B ≃ₐ[A] B
  let gg : Group G := inferInstanceAs (Group (B ≃ₐ[A] B))
  let act : MulSemiringAction G B :=
    inferInstanceAs (MulSemiringAction (B ≃ₐ[A] B) B)
  have fG : Finite G := inferInstance
  let e (σ : G) : B ≃+* B :=
    RingEquiv.ofBijective (MulSemiringAction.toRingHom G B σ)
      (MulDistribMulAction.toMulEquiv B σ).bijective
  have he (σ : G) : e σ = (σ : B ≃ₐ[A] B).toRingEquiv := by
    apply RingEquiv.ext
    intro b
    rfl
  have horders : ∀ (σ : G) (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
      (hσ : Q = Q.comap (e σ).toRingHom),
      (∀ (p : ℕ) [Fact p.Prime]
        [CharP (IsLocalRing.ResidueField (Localization.AtPrime Q)) p],
        (∀ x : Localization.AtPrime Q, ∃ a : (Localization.AtPrime Q)ˣ,
          Localization.localRingEquiv Q Q (e σ) hσ x =
            x * (a : Localization.AtPrime Q) ∧
            (a : Localization.AtPrime Q) - 1 ∈
              IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
        ∃ n : ℕ, σ ^ (p ^ n) = 1) ∧
      (∀ [CharZero (IsLocalRing.ResidueField (Localization.AtPrime Q))],
        (∀ x : Localization.AtPrime Q, ∃ a : (Localization.AtPrime Q)ˣ,
          Localization.localRingEquiv Q Q (e σ) hσ x =
            x * (a : Localization.AtPrime Q) ∧
            (a : Localization.AtPrime Q) - 1 ∈
              IsLocalRing.maximalIdeal (Localization.AtPrime Q)) → σ = 1) := by
    intro σ Q qPrime hQ hσ
    have hσ' : Q = Q.comap (σ : B ≃ₐ[A] B).toRingEquiv.toRingHom := by
      simpa only [he σ] using hσ
    have h := integralAutomorphism_localized_principal_order A B σ Q hQ hσ'
    constructor
    · intro p hp hchar hprincipal
      obtain ⟨n, hn⟩ := h.1 p (by simpa only [he σ] using hprincipal)
      clear hprincipal h hσ hσ' hQ qPrime hchar Q
      refine ⟨n, ?_⟩
      apply AlgEquiv.ext
      intro b
      have hb := RingEquiv.congr_fun hn b
      have hi : (⇑(σ : B ≃ₐ[A] B))^[p ^ n] b = b := by
        simpa only [RingAut.coe_pow, AlgEquiv.coe_ringEquiv, RingAut.one_apply] using hb
      exact (congrFun (AlgEquiv.coe_pow (σ : B ≃ₐ[A] B) (p ^ n)) b).trans hi
    · intro hchar hprincipal
      have hn : (σ : B ≃ₐ[A] B).toRingEquiv = RingEquiv.refl B :=
        h.2 (by simpa only [he σ] using hprincipal)
      clear hprincipal h hσ hσ' hQ qPrime hchar Q
      exact AlgEquiv.coe_ringEquiv_injective hn
  clear he
  change ∀ (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥),
    ∃ n : ℕ, finiteIdealWildOrder B G Q hQ = (ringExpChar Q.ResidueField) ^ n
  clear_value act
  clear_value gg
  clear_value G
  clear finAB tfAB aAB dA rA A
  intro Q qPrime hQ
  have dvr : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      B hQ (Localization.AtPrime Q)
  by_cases hchar : ringChar Q.ResidueField = 0
  · have hc : CharZero Q.ResidueField :=
      (CharP.ringChar_zero_iff_CharZero (R := Q.ResidueField)).mp hchar
    have hlocal : ∀ σ : MulAction.stabilizer G Q,
        (∀ x : Localization.AtPrime Q, ∃ a : (Localization.AtPrime Q)ˣ,
          σ • x = x * (a : Localization.AtPrime Q) ∧
            (a : Localization.AtPrime Q) - 1 ∈
              IsLocalRing.maximalIdeal (Localization.AtPrime Q)) → (σ : G) = 1 := by
      intro σ hprincipal
      exact (horders σ Q hQ
        (SchemeTheory.stabilizerCoefficientRingEquiv_comap_eq B G Q σ)).2 hprincipal
    refine ⟨0, ?_⟩
    rw [pow_zero]
    clear horders e hchar hc
    change Nat.card
      (principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q)) = 1
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, ?_⟩
    intro σ
    have hprincipal := (mem_principalUnitInertia_iff_sub_one_mem
      (Localization.AtPrime Q) (MulAction.stabilizer G Q) σ.val).mp σ.property
    have hg : (σ.val.val : G) = 1 := hlocal σ.val.val hprincipal
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hg
  · let p := ringChar Q.ResidueField
    have hp : p.Prime := CharP.char_prime_of_ne_zero Q.ResidueField hchar
    have fp : Fact p.Prime := ⟨hp⟩
    have hlocal : ∀ σ : MulAction.stabilizer G Q,
        (∀ x : Localization.AtPrime Q, ∃ a : (Localization.AtPrime Q)ˣ,
          σ • x = x * (a : Localization.AtPrime Q) ∧
            (a : Localization.AtPrime Q) - 1 ∈
              IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
        ∃ n : ℕ, (σ : G) ^ (p ^ n) = 1 := by
      intro σ hprincipal
      exact (horders σ Q hQ
        (SchemeTheory.stabilizerCoefficientRingEquiv_comap_eq B G Q σ)).1 p hprincipal
    have hexp : ringExpChar Q.ResidueField = p := Nat.max_eq_left hp.one_lt.le
    rw [hexp]
    clear horders e hexp hchar hp
    clear_value p
    change ∃ n : ℕ,
      Nat.card (principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q)) = p ^ n
    have hP : IsPGroup p
        (principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q)) := by
      apply isPGroup_iff_pow_pow_eq_one.mpr
      intro σ
      have hprincipal := (mem_principalUnitInertia_iff_sub_one_mem
        (Localization.AtPrime Q) (MulAction.stabilizer G Q) σ.val).mp σ.property
      obtain ⟨n, hn⟩ := hlocal σ.val.val hprincipal
      refine ⟨n, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hn
    exact IsPGroup.iff_card.mp hP

end EtaleFundamentalGroups.Inertia
