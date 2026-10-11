/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.Tactic.Push

/-!
# Witt Vector exists valuation Subring residue Field equiv of is Algebraic
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic

open IsLocalRing Polynomial

namespace WittVector
open _root_.WittVector
namespace WittBase
open _root_.WittVector

section General

theorem mem_range_of_eval₂_eq_zero {k K' : Type*} [Field k] [IsAlgClosed k] [Field K']
    (f : k →+* K') {q : k[X]} (hq : q ≠ 0) {z : K'} (hz : q.eval₂ f z = 0) : z ∈ Set.range f := by
  let : Algebra k K' := f.toAlgebra
  have hint : IsIntegral k z := isAlgebraic_iff_isIntegral.mp ⟨q, hq, hz⟩
  have : FiniteDimensional k (IntermediateField.adjoin k {z}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hbot : IntermediateField.adjoin k {z} = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  have hz' : z ∈ (⊥ : IntermediateField k K') := hbot ▸ IntermediateField.mem_adjoin_simple_self k z
  rwa [IntermediateField.mem_bot] at hz'

theorem exists_eq_C_mul_and_isUnit_coeff {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {g : R[X]} (hg : g ≠ 0) :
    ∃ (c : R) (g₁ : R[X]) (i : ℕ), c ≠ 0 ∧ g = C c * g₁ ∧ IsUnit (g₁.coeff i) := by
  classical
  let : NormalizationMonoid R :=
    UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid
  let : NormalizedGCDMonoid R := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  by_contra hall
  push Not at hall
  have hmem : ∀ j, g.primPart.coeff j ∈ maximalIdeal R := fun j =>
    (mem_maximalIdeal _).mpr
      (hall _ _ j (content_eq_zero_iff.not.mpr hg) g.eq_C_content_mul_primPart)
  have hdvd : C ϖ ∣ g.primPart := (C_dvd_iff_dvd_coeff ϖ _).mpr fun j => by
    have h := hmem j
    rw [hmax, Ideal.mem_span_singleton] at h
    exact h
  exact hϖ.not_isUnit (g.isPrimitive_primPart ϖ hdvd)

end General

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]

theorem maximalIdeal_eq : maximalIdeal (WittVector p k) = Ideal.span {(p : WittVector p k)} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (WittVector.irreducible (p := p))

theorem maximalIdeal_eq_ker :
    maximalIdeal (WittVector p k) = RingHom.ker (WittVector.constantCoeff : WittVector p k →+* k)
      := by
  rw [maximalIdeal_eq, WittVector.ker_constantCoeff]

/-- Identify the residue field of the Witt-vector ring with its coefficient field via the
constant coefficient. -/
noncomputable def resEquivInv : ResidueField (WittVector p k) ≃+* k :=
  (Ideal.quotEquivOfEq (maximalIdeal_eq_ker p k)).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (WittVector.constantCoeff : WittVector p k →+* k)) (WittVector.constantCoeff_surjective
        p))

theorem resEquivInv_residue (a : WittVector p k) :
    resEquivInv p k (residue (WittVector p k) a) = a.coeff 0 := by
  change RingHom.quotientKerEquivOfSurjective (f := (WittVector.constantCoeff : WittVector p k →+*
    k))
      (WittVector.constantCoeff_surjective p)
      (Ideal.quotEquivOfEq (maximalIdeal_eq_ker p k) (Ideal.Quotient.mk _ a)) = _
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    WittVector.constantCoeff_apply]

/-- The inverse ring equivalence from the coefficient field to the residue field of its
Witt-vector ring. -/
noncomputable def residueEquiv : k ≃+* ResidueField (WittVector p k) := (resEquivInv p k).symm

theorem residueEquiv_coeff_zero (a : WittVector p k) :
    residueEquiv p k (a.coeff 0) = residue (WittVector p k) a := by
  rw [residueEquiv, ← resEquivInv_residue p k a, RingEquiv.symm_apply_apply]

variable (Ω : Type*) [Field Ω] [Algebra (WittVector p k) Ω] [FaithfulSMul (WittVector p k) Ω]
  [Algebra.IsAlgebraic (WittVector p k) Ω]

theorem main :
    ∃ (V : ValuationSubring Ω) (hV : ∀ a : WittVector p k, algebraMap (WittVector p k) Ω a ∈ V)
      (φ : k ≃+* ResidueField V),
      (∀ a ∈ maximalIdeal (WittVector p k), algebraMap (WittVector p k) Ω a ∈ V.nonunits) ∧
      ∀ a : WittVector p k, φ (a.coeff 0) = residue V ⟨algebraMap (WittVector p k) Ω a, hV a⟩ := by
  classical
  have hinj : Function.Injective (algebraMap (WittVector p k) Ω) :=
    FaithfulSMul.algebraMap_injective _ _
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap (WittVector p k) Ω)
  set f : WittVector p k →+* V := (algebraMap (WittVector p k) Ω).codRestrict V.toSubring hV with hf
  have : IsLocalHom f := hloc
  have hfval : ∀ a : WittVector p k, ((f a : V) : Ω) = algebraMap (WittVector p k) Ω a := fun a =>
    rfl
  have hdom : ∀ a ∈ maximalIdeal (WittVector p k), algebraMap (WittVector p k) Ω a ∈ V.nonunits :=
    by
    intro a ha
    rw [← hfval, ValuationSubring.coe_mem_nonunits_iff]
    exact map_nonunit f a ha
  set φ₀ : k →+* ResidueField V := (ResidueField.map f).comp (residueEquiv p k).toRingHom with hφ₀
  have hφ₀a : ∀ a : WittVector p k, φ₀ (a.coeff 0) = residue V (f a) := by
    intro a
    simp only [hφ₀, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, residueEquiv_coeff_zero]
    rfl
  have hsurj : Function.Surjective φ₀ := by
    intro y
    obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective y
    have halg : IsAlgebraic (WittVector p k) (v : Ω) := Algebra.IsAlgebraic.isAlgebraic _
    obtain ⟨g, hg0, hgv⟩ := halg
    obtain ⟨c, g₁, i, hc, hgc, hunit⟩ := exists_eq_C_mul_and_isUnit_coeff hg0
    have hg₁v : aeval (v : Ω) g₁ = 0 := by
      rw [hgc, map_mul, aeval_C, mul_eq_zero] at hgv
      exact hgv.resolve_left ((map_ne_zero_iff _ hinj).mpr hc)
    have hcomp : V.subtype.comp f = algebraMap (WittVector p k) Ω := RingHom.ext fun a => rfl
    have hg₁V : (g₁.map f).eval v = 0 := by
      apply Subtype.val_injective
      rw [eval_map, show (((g₁.eval₂ f v : V)) : Ω) = V.subtype (g₁.eval₂ f v) from rfl,
        hom_eval₂ g₁ f V.subtype v, hcomp]
      rw [aeval_def] at hg₁v
      simpa using hg₁v
    set q : k[X] := (g₁.map (residue (WittVector p k))).map (residueEquiv p k).symm.toRingHom with
      hq
    have hqi : q.coeff i ≠ 0 := by
      rw [hq, coeff_map, coeff_map]
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ne_eq,
        EmbeddingLike.map_eq_zero_iff, residue_eq_zero_iff]
      exact fun hmem => (mem_maximalIdeal _).mp hmem hunit
    have hq0 : q ≠ 0 := fun h => hqi (by rw [h, coeff_zero])
    have hqeval : q.eval₂ φ₀ (residue V v) = 0 := by
      have e1 : q.eval₂ φ₀ (residue V v) = (g₁.map (residue (WittVector p k))).eval₂
        (ResidueField.map f)
          (residue V v) := by
        rw [hq, eval₂_map]
        congr 1
        ext x
        simp [hφ₀]
      have e2 : (g₁.map (residue (WittVector p k))).eval₂ (ResidueField.map f) (residue V v) =
          (g₁.map f).eval₂ (residue V) (residue V v) := by
        rw [eval₂_map, eval₂_map]
        congr 1
      have h3 := Polynomial.hom_eval₂ (g₁.map f) (RingHom.id V) (residue V) v
      rw [RingHom.comp_id] at h3
      rw [e1, e2, ← h3]
      change residue V ((g₁.map f).eval v) = 0
      rw [hg₁V, map_zero]
    obtain ⟨x, hx⟩ := mem_range_of_eval₂_eq_zero φ₀ hq0 hqeval
    exact ⟨x, hx⟩
  refine ⟨V, hV, RingEquiv.ofBijective φ₀ ⟨φ₀.injective, hsurj⟩, hdom, fun a => ?_⟩
  exact hφ₀a a

end WittVector.WittBase

theorem _root_.WittVector.exists_valuationSubring_residueField_equiv_of_isAlgebraic (p : ℕ) [Fact
  p.Prime] (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (Ω : Type*) [Field Ω] [Algebra
  (WittVector p k) Ω] [FaithfulSMul (WittVector p k) Ω] [Algebra.IsAlgebraic (WittVector p k) Ω] :
  ∃ (V : ValuationSubring Ω) (hV : ∀ a : WittVector p k, algebraMap (WittVector p k) Ω a ∈ V) (φ :
  k ≃+* IsLocalRing.ResidueField V), (∀ a ∈ IsLocalRing.maximalIdeal (WittVector p k), algebraMap
  (WittVector p k) Ω a ∈ V.nonunits) ∧ ∀ a : WittVector p k, φ (a.coeff 0) = IsLocalRing.residue V
  ⟨algebraMap (WittVector p k) Ω a, hV a⟩ :=
  WittVector.WittBase.main p k Ω
end WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
