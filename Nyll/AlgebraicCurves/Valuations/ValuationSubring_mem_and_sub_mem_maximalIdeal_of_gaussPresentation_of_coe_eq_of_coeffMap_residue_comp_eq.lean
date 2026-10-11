/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_mem_and_sub_mem_maximalIdeal_of_gaussPresentation_of_coe_eq_of_coeffMap_residue_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.LaurentBaseChange
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Valuation Subring mem and sub mem maximal Ideal of gauss Presentation of coe eq of coeff
Map residue comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs.GaussPresentationResidues

open ModularCurve IsLocalRing

namespace IgResid

section algebra

variable {M : Type*} [CommRing M]

private theorem presentation_sub {F TF a b a' b' : M} (h1 : F * b = a) (h2 : TF * b' = a') :
    (TF - F) * (b * b') = a' * b - a * b' := by
  linear_combination b * h2 - b' * h1

private theorem key_identity {g v a b a' b' : M} (hgp : g * b = a) (hvy : v * b' = a') (hv : g * v
  = 1) :
    b * b' = a * a' := by
  calc b * b' = (g * v) * (b * b') := by rw [hv, one_mul]
    _ = (g * b) * (v * b') := by ring
    _ = a * a' := by rw [hgp, hvy]

end algebra

section coeff

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) : Function.Injective
  (coeffMap f) := by
  intro a b h
  ext k
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff k) h
  simpa using this

end coeff

end IgResid
end AlgebraicCurves.Valuations.Proofs.GaussPresentationResidues

namespace ValuationSubring

open _root_.AlgebraicCurves.Valuations.Proofs.GaussPresentationResidues
open _root_.ModularCurve _root_.IsLocalRing


open _root_.AlgebraicCurves.Valuations.Proofs.GaussPresentationResidues.IgResid in
theorem mem_and_sub_mem_maximalIdeal_of_gaussPresentation_of_coe_eq_of_coeffMap_residue_comp_eq
    {L : Type} [Field L] (A : ValuationSubring L)
    (F : IntermediateField L (LaurentSeries L))
    (O : ValuationSubring F)
    (hO : ∀ f : F, f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x)
    (Φ : LaurentSeries L →+* LaurentSeries L) (Ψ : LaurentSeries A →+* LaurentSeries A)
    (hΦΨ : ∀ y : LaurentSeries A, Φ (coeffMap A.subtype y) = coeffMap A.subtype (Ψ y))
    (hΨ : ∀ y : LaurentSeries A, coeffMap (IsLocalRing.residue A) (Ψ y) = coeffMap
      (IsLocalRing.residue A) y)
    (T : F →+* F) (hT : ∀ f : F, ((T f : F) : LaurentSeries L) = Φ (f : LaurentSeries L))
    (f : F) (hf : f ∈ O) :
    ∃ hTf : T f ∈ O, (⟨T f, hTf⟩ : O) - ⟨f, hf⟩ ∈ IsLocalRing.maximalIdeal O := by
  obtain ⟨x, y, hy, hfy⟩ := (hO f).mp hf
  have hTfy : ((T f : F) : LaurentSeries L) * coeffMap A.subtype (Ψ y) = coeffMap A.subtype (Ψ x)
    := by
    rw [hT, ← hΦΨ, ← hΦΨ, ← map_mul, hfy]
  have hΨy : coeffMap (IsLocalRing.residue A) (Ψ y) ≠ 0 := by rwa [hΨ]
  have hTf : T f ∈ O := (hO (T f)).mpr ⟨Ψ x, Ψ y, hΨy, hTfy⟩
  refine ⟨hTf, ?_⟩
  have hnum0 : coeffMap (IsLocalRing.residue A) (Ψ x * y - x * Ψ y) = 0 := by
    rw [map_sub, map_mul, map_mul, hΨ, hΨ, sub_self]
  have hden0 : coeffMap (IsLocalRing.residue A) (y * Ψ y) ≠ 0 := by
    rw [map_mul, hΨ]
    exact mul_ne_zero hy hy
  have hgp : ((T f - f : F) : LaurentSeries L) * coeffMap A.subtype (y * Ψ y) =
      coeffMap A.subtype (Ψ x * y - x * Ψ y) := by
    rw [AddSubgroupClass.coe_sub, map_mul, map_sub, map_mul, map_mul]
    exact presentation_sub hfy hTfy
  have hgO : T f - f ∈ O := (hO (T f - f)).mpr ⟨Ψ x * y - x * Ψ y, y * Ψ y, hden0, hgp⟩
  have hgnu : ¬ IsUnit (⟨T f - f, hgO⟩ : O) := by
    intro hunit
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    obtain ⟨x', y', hy', hvy⟩ := (hO (v : F)).mp v.2
    have hvF : (T f - f) * (v : F) = 1 := congrArg Subtype.val hv
    have hv' : ((T f - f : F) : LaurentSeries L) * ((v : F) : LaurentSeries L) = 1 := by
      rw [← MulMemClass.coe_mul, hvF, OneMemClass.coe_one]
    have key := key_identity hgp hvy hv'
    rw [← map_mul, ← map_mul] at key
    have key' := coeffMap_injective Subtype.val_injective key
    have h2 := congrArg (coeffMap (IsLocalRing.residue A)) key'
    rw [map_mul _ (y * Ψ y) y', map_mul _ (Ψ x * y - x * Ψ y) x', hnum0, zero_mul] at h2
    exact mul_ne_zero hden0 hy' h2
  have hsub : (⟨T f, hTf⟩ : O) - ⟨f, hf⟩ = ⟨T f - f, hgO⟩ := Subtype.ext rfl
  rw [hsub, IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
  exact hgnu
end ValuationSubring
end ProofImplementation
