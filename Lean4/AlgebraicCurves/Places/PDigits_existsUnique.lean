/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_pDigits_existsUnique.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import AlgebraicCurves.Places.ExistsUnique_pDigits_of_transcendental
import AlgebraicCurves.FunctionFields.FiniteDimensional_adjoin_of_transcendental

/-!
# PDigits exists Unique
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.PDigits_existsUnique

universe u v

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

private theorem transcendental_of_D_ne_zero' [PerfectField K] {t : F}
    (hdt : D K F t ≠ 0) : Transcendental K t := by
  by_contra htr
  rw [Transcendental, not_not] at htr
  have hint : IsIntegral K t := htr.isIntegral
  have hirr := minpoly.irreducible hint
  have hsep : (minpoly K t).Separable := PerfectField.separable_of_irreducible hirr
  have hd0 : (Polynomial.aeval t) (Polynomial.derivative (minpoly K t)) ≠ 0 := by
    intro h0
    by_cases hder : Polynomial.derivative (minpoly K t) = 0
    · exact hirr.1 (isCoprime_zero_right.mp (hder ▸ hsep))
    · exact absurd (Polynomial.degree_le_of_dvd (minpoly.dvd K t h0) hder)
        (not_le.2 (Polynomial.degree_derivative_lt (minpoly.ne_zero hint)))
  apply hdt
  have h0 : (D K F) ((Polynomial.aeval t) (minpoly K t)) = 0 := by
    rw [minpoly.aeval, map_zero]
  rw [Derivation.map_aeval] at h0
  exact (smul_eq_zero.mp h0).resolve_left hd0

private theorem pow_ne_of_D_ne_zero' (p : ℕ) [Fact p.Prime] [CharP K p] {t : F}
    (hdt : D K F t ≠ 0) (a : F) : a ^ p ≠ t := by
  intro ha
  apply hdt
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  rw [← ha, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]

private theorem pDigits_existsUnique_impl [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (hdt : D K F t ≠ 0) (g : F) :
    ∃! a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by
  have htr : Transcendental K t := transcendental_of_D_ne_zero' hdt
  have : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
    finiteDimensional_adjoin_of_transcendental x htr
  exact existsUnique_pDigits_of_transcendental p t htr (pow_ne_of_D_ne_zero' p hdt) g

end AlgebraicCurve

theorem _root_.AlgebraicCurve.pDigits_existsUnique {K : Type u} {F : Type v} [Field K] [Field F]
    [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (hdt : D K F t ≠ 0) (g : F) :
    ∃! a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) :=
  AlgebraicCurve.pDigits_existsUnique_impl p x hdt g
end AlgebraicCurves.Places.Proofs.PDigits_existsUnique
end ProofImplementation
