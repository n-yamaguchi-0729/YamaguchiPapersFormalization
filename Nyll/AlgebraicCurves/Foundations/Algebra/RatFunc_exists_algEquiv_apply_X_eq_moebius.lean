/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Rat Func exists alg Equiv apply X eq moebius
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.RatFunc_exists_algEquiv_apply_X_eq_moebius

open Polynomial IntermediateField

namespace RatFunc
open _root_.RatFunc
open _root_.RatFunc

variable {K : Type*} [Field K]

theorem moebius_aux (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    ∃ φ : RatFunc K ≃ₐ[K] RatFunc K,
      φ RatFunc.X = (RatFunc.C a * RatFunc.X + RatFunc.C b) / (RatFunc.C c * RatFunc.X + RatFunc.C
        d) := by
  set f : RatFunc K := (RatFunc.C a * RatFunc.X + RatFunc.C b) / (RatFunc.C c * RatFunc.X +
    RatFunc.C d) with hf
  have hden : (RatFunc.C c * RatFunc.X + RatFunc.C d : RatFunc K) ≠ 0 := by
    intro h
    have h1 : (RatFunc.C c * RatFunc.X + RatFunc.C d : RatFunc K) = algebraMap K[X] (RatFunc K)
      (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
      simp [map_add, map_mul]
    rw [h1, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))] at h
    have hc : c = 0 := by simpa using congrArg (fun p : K[X] ↦ p.coeff 1) h
    have hd : d = 0 := by simpa using congrArg (fun p : K[X] ↦ p.coeff 0) h
    apply hdet; rw [hc, hd]; ring
  have hkey : (RatFunc.C a - RatFunc.C c * f) * (RatFunc.C c * RatFunc.X + RatFunc.C d) = RatFunc.C
    (a * d - b * c) := by
    rw [hf, sub_mul, mul_assoc, div_mul_cancel₀ _ hden, map_sub, map_mul, map_mul]; ring
  have hac : (RatFunc.C a - RatFunc.C c * f : RatFunc K) ≠ 0 := by
    intro h; rw [h, zero_mul, eq_comm, map_eq_zero_iff _ RatFunc.C_injective] at hkey; exact hdet
      hkey
  have hX : (RatFunc.X : RatFunc K) = (RatFunc.C d * f - RatFunc.C b) / (RatFunc.C a - RatFunc.C c
    * f) := by
    rw [eq_div_iff hac]
    have : (RatFunc.C d * f - RatFunc.C b) * (RatFunc.C c * RatFunc.X + RatFunc.C d) = RatFunc.X *
      RatFunc.C (a * d - b * c) := by
      rw [sub_mul, mul_assoc, hf, div_mul_cancel₀ _ hden, map_sub, map_mul, map_mul]; ring
    have h2 := congrArg (· * (RatFunc.C c * RatFunc.X + RatFunc.C d)) (show (RatFunc.X : RatFunc K)
      * (RatFunc.C a - RatFunc.C c * f) = RatFunc.X * (RatFunc.C a - RatFunc.C c * f) from rfl)
    apply mul_right_cancel₀ hden
    rw [mul_assoc, hkey, this]
  have hfC : ¬ ∃ e : K, f = RatFunc.C e := by
    rintro ⟨e, he⟩
    have : ∃ e' : K, (RatFunc.X : RatFunc K) = RatFunc.C e' := by
      refine ⟨(d * e - b) / (a - c * e), ?_⟩
      rw [hX, he, ← map_mul, ← map_sub, ← map_mul, ← map_sub, ← map_div₀]
    obtain ⟨e', he'⟩ := this
    have halg : IsAlgebraic K (RatFunc.X : RatFunc K) := by
      rw [he', ← RatFunc.algebraMap_eq_C]
      exact isAlgebraic_algebraMap e'
    exact RatFunc.transcendental_X halg
  have htr : Transcendental K f := transcendental_of_ne_C f hfC
  have hXmem : (RatFunc.X : RatFunc K) ∈ K⟮f⟯ := by
    rw [hX]
    have hfmem : f ∈ K⟮f⟯ := mem_adjoin_simple_self K f
    have hCmem : ∀ e : K, (RatFunc.C e : RatFunc K) ∈ K⟮f⟯ := fun e ↦ by
      rw [← algebraMap_C]; exact (K⟮f⟯).algebraMap_mem e
    exact div_mem (sub_mem (mul_mem (hCmem d) hfmem) (hCmem b)) (sub_mem (hCmem a) (mul_mem (hCmem
      c) hfmem))
  have htop : K⟮f⟯ = ⊤ := by
    rw [eq_top_iff, ← RatFunc.adjoin_X (K := K), adjoin_simple_le_iff]
    exact hXmem
  refine ⟨(algEquivOfTranscendental f htr).trans ((equivOfEq htop).trans topEquiv), ?_⟩
  simp [algEquivOfTranscendental_X]

end RatFunc

theorem _root_.RatFunc.exists_algEquiv_apply_X_eq_moebius {K : Type*} [Field K] (a b c d : K) (hdet
  : a * d - b * c ≠ 0) : ∃ φ : RatFunc K ≃ₐ[K] RatFunc K, φ RatFunc.X = (RatFunc.C a * RatFunc.X +
  RatFunc.C b) / (RatFunc.C c * RatFunc.X + RatFunc.C d) :=
  RatFunc.moebius_aux a b c d hdet

end AlgebraicCurves.Foundations.Algebra.Proofs.RatFunc_exists_algEquiv_apply_X_eq_moebius
end ProofImplementation
