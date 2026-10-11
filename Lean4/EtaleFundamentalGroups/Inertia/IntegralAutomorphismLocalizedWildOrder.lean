/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.IntegralAutomorphismWildLift
import SchemeTheory.RingTheory.Ramification.IdealLocalizationPrincipalTransport
import SchemeTheory.RingTheory.Ramification.LocalRingResidueCharacteristicTransport
import SchemeTheory.RingTheory.Ramification.RingActionOrderReflection

/-!
# Orders of localized principal-unit automorphisms

Proves a residue-characteristic power order law for intrinsic normalization automorphisms whose
prime localizations act by principal units, including triviality in residue characteristic zero.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open TameAbhyankar.SGA1

universe u v

/-- The original intrinsic normalization automorphism has p-power order,
or is trivial in residue characteristic zero, when its actual prime
localization acts by principal units. Every field/action comparison comes
from the actual fraction lift and canonical localization equivalence. -/
theorem integralAutomorphism_localized_principal_order
    (A : Type u) (B : Type v)
    [rA : CommRing A] [dA : IsDomain A]
    [rB : CommRing B] [dB : IsDedekindDomain B]
    [aAB : Algebra A B] [finAB : Module.Finite A B] [tfAB : Module.IsTorsionFree A B]
    (σ : B ≃ₐ[A] B) :
    ∀ (Q : Ideal B) [Q.IsPrime], Q ≠ ⊥ →
      ∀ (hσ : Q = Q.comap σ.toRingEquiv.toRingHom),
      (∀ (p : ℕ) [Fact p.Prime]
        [CharP (IsLocalRing.ResidueField (Localization.AtPrime Q)) p],
        (∀ x : Localization.AtPrime Q, ∃ a : (Localization.AtPrime Q)ˣ,
          Localization.localRingEquiv Q Q σ.toRingEquiv hσ x =
            x * (a : Localization.AtPrime Q) ∧
            (a : Localization.AtPrime Q) - 1 ∈
              IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
        ∃ n : ℕ, σ.toRingEquiv ^ (p ^ n) = 1) ∧
      (∀ [CharZero (IsLocalRing.ResidueField (Localization.AtPrime Q))],
        (∀ x : Localization.AtPrime Q, ∃ a : (Localization.AtPrime Q)ˣ,
          Localization.localRingEquiv Q Q σ.toRingEquiv hσ x =
            x * (a : Localization.AtPrime Q) ∧
            (a : Localization.AtPrime Q) - 1 ∈
              IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
        σ.toRingEquiv = 1) := by
  obtain ⟨L, lField, bL, hfrac, ρ, hcoeff, hpositive, hzero⟩ :=
    integralAutomorphism_exists_wild_fraction_lift A B σ
  have hcoeff' : ρ.toRingHom.comp (algebraMap B L) =
      (algebraMap B L).comp σ.toRingEquiv.toRingHom := hcoeff
  generalize hσB : σ.toRingEquiv = δ at hcoeff' ⊢
  clear hcoeff hσB σ finAB tfAB aAB dA rA A
  intro Q qPrime hQ hδ
  constructor
  · intro p hp hchar
    let V := idealLocalizationValuationSubring B L Q hQ
    have hvchar : CharP (IsLocalRing.ResidueField V) p :=
      SchemeTheory.residueField_charP_of_ringEquiv
        (primeLocalizationEquivValuation B L Q hQ) p
    have horder := hpositive V p
    clear hchar hvchar hpositive hzero
    intro hprincipal
    obtain ⟨τ, hfield, hτ⟩ := idealLocalization_exists_principal_valuation_action
      B L Q hQ δ hδ ρ.toRingHom hcoeff' hprincipal
    clear hprincipal
    obtain ⟨n, hn⟩ := horder τ.toRingHom τ.surjective hfield hτ
    exact ⟨n, SchemeTheory.ringEquiv_pow_eq_one_of_extension
      (algebraMap B L) (IsFractionRing.injective B L)
      δ ρ hcoeff' (p ^ n) hn⟩
  · intro hchar
    let V := idealLocalizationValuationSubring B L Q hQ
    have hvchar : CharZero (IsLocalRing.ResidueField V) :=
      SchemeTheory.residueField_charZero_of_ringEquiv
        (primeLocalizationEquivValuation B L Q hQ)
    have horder : ∀ (τ : V →+* V), Function.Surjective τ →
        V.subtype.comp τ = ρ.toRingHom.comp V.subtype →
        (∀ x : V, ∃ a : Vˣ, τ x = x * (a : V) ∧
          (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) →
        ρ = RingEquiv.refl L := hzero V
    clear hchar hvchar hpositive hzero
    intro hprincipal
    obtain ⟨τ, hfield, hτ⟩ := idealLocalization_exists_principal_valuation_action
      B L Q hQ δ hδ ρ.toRingHom hcoeff' hprincipal
    clear hprincipal
    have hρ := horder τ.toRingHom τ.surjective hfield hτ
    have hδone := SchemeTheory.ringEquiv_pow_eq_one_of_extension
      (algebraMap B L) (IsFractionRing.injective B L)
      δ ρ hcoeff' 1 (by
        rw [pow_one, hρ]
        rfl)
    rwa [pow_one] at hδone

end EtaleFundamentalGroups.Inertia
