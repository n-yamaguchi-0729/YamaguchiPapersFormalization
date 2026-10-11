/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.IntegralAutomorphismFiniteFieldLift
import ValuedFieldTheory.Ramification.HilbertRamification.FieldPrincipalWildOrder
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.Aut

/-!
# Wild order laws for fraction-field lifts

Constructs a finite fraction-field lift of an integral automorphism together with the local
principal-unit order laws.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

/-- The actually constructed finite fraction-field lift satisfies the local
principal-unit order laws. Its existential field data is abstract, so the
original coefficient ring is cleared before either local order proof. -/
theorem integralAutomorphism_exists_wild_fraction_lift
    (A : Type u) (B : Type v)
    [rA : CommRing A] [dA : IsDomain A]
    [rB : CommRing B] [dB : IsDedekindDomain B]
    [aAB : Algebra A B] [finAB : Module.Finite A B] [tfAB : Module.IsTorsionFree A B]
    (σ : B ≃ₐ[A] B) :
    ∃ (L : Type v) (lField : Field L),
      let : Field L := lField
      ∃ (bL : Algebra B L),
        let : Algebra B L := bL
        IsFractionRing B L ∧ ∃ ρ : L ≃+* L,
          ρ.toRingHom.comp (algebraMap B L) =
            (algebraMap B L).comp σ.toRingHom ∧
          (∀ (V : _root_.ValuationSubring L) (p : ℕ)
            [Fact p.Prime] [CharP (IsLocalRing.ResidueField V) p]
            (τ : V →+* V), Function.Surjective τ →
            V.subtype.comp τ = ρ.toRingHom.comp V.subtype →
            (∀ x : V, ∃ a : Vˣ,
              τ x = x * (a : V) ∧ (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) →
            ∃ n : ℕ, ρ ^ (p ^ n) = 1) ∧
          (∀ (V : _root_.ValuationSubring L)
            [CharZero (IsLocalRing.ResidueField V)]
            (τ : V →+* V), Function.Surjective τ →
            V.subtype.comp τ = ρ.toRingHom.comp V.subtype →
            (∀ x : V, ∃ a : Vˣ,
              τ x = x * (a : V) ∧ (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) →
            ρ = 1) := by
  obtain ⟨K, L, kField, lField, bL, kL, hfrac, fd, ρAlg, hcoeff⟩ :=
    integralAutomorphism_exists_finite_field_lift A B σ
  generalize hσB : σ.toRingHom = σB at hcoeff ⊢
  clear hσB σ finAB tfAB aAB dA rA A
  refine ⟨L, lField, bL, hfrac, ρAlg.toRingEquiv, hcoeff, ?_, ?_⟩
  · clear hcoeff σB hfrac bL dB rB B
    intro V p hp hchar τ hτ hfield hprincipal
    obtain ⟨n, hn⟩ := fieldAutomorphism_pow_prime_eq_one_of_local_principal_units
      K V p ρAlg τ hτ hfield hprincipal
    clear hprincipal hfield hτ τ hchar hp V
    refine ⟨n, ?_⟩
    apply RingEquiv.ext
    intro x
    have hx := congrArg (fun f : L ≃ₐ[K] L => f x) hn
    simpa only [AlgEquiv.coe_pow, RingAut.coe_pow, AlgEquiv.coe_ringEquiv,
      AlgEquiv.one_apply, RingAut.one_apply] using hx
  · change ∀ (V : _root_.ValuationSubring L)
        [CharZero (IsLocalRing.ResidueField V)] (τ : V →+* V),
        Function.Surjective τ →
        V.subtype.comp τ = ρAlg.toRingHom.comp V.subtype →
        (∀ x : V, ∃ a : Vˣ, τ x = x * (a : V) ∧
          (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) →
        ρAlg.toRingEquiv = RingEquiv.refl L
    clear hcoeff σB hfrac bL dB rB B
    intro V hchar τ hτ hfield hprincipal
    exact congrArg (fun f : L ≃ₐ[K] L => f.toRingEquiv)
      (fieldAutomorphism_eq_one_of_local_principal_units_charZero
        K V ρAlg τ hτ hfield hprincipal)

end EtaleFundamentalGroups.Inertia
