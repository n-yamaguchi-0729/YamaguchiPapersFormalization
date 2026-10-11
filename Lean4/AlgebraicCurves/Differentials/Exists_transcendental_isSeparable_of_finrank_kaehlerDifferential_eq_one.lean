/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
Find a separable transcendental coordinate when the differential module has rank one.
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs
namespace Exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one

universe u v

open IntermediateField

theorem
    _root_.AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [Algebra.EssFiniteType K F]
    [Algebra.Transcendental K F] (hΩ : Module.finrank F Ω[F⁄K] = 1) :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by
    by_contra h
    push Not at h
    have htop : (⊤ : Submodule F Ω[F⁄K]) = ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
      rintro _ ⟨x, rfl⟩
      exact h x
    have h0 : Module.finrank F Ω[F⁄K] = 0 := by
      rw [← finrank_top, htop, finrank_bot]
    omega
  have hspan : ∀ ω : Ω[F⁄K], ∃ c : F, c • KaehlerDifferential.D K F t = ω :=
    (finrank_eq_one_iff_of_nonzero' _ ht).mp hΩ
  have hDt : KaehlerDifferential.D K⟮t⟯ F t = 0 := by
    have h := (KaehlerDifferential.D K⟮t⟯ F).map_algebraMap (AdjoinSimple.gen K t)
    rwa [AdjoinSimple.algebraMap_gen] at h
  have hsub : Subsingleton Ω[F⁄K⟮t⟯] := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    obtain ⟨ω₀, rfl⟩ := KaehlerDifferential.map_surjective K K⟮t⟯ F ω
    obtain ⟨c, rfl⟩ := hspan ω₀
    rw [map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply, hDt,
      smul_zero]
  have : Algebra.FormallyUnramified K⟮t⟯ F := ⟨hsub⟩
  have : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  have hsep : Algebra.IsSeparable K⟮t⟯ F := Algebra.FormallyUnramified.isSeparable K⟮t⟯ F
  have hfin : Module.Finite K⟮t⟯ F := Algebra.FormallyUnramified.finite_of_free K⟮t⟯ F
  refine ⟨t, ?_, hfin, hsep⟩
  change ¬IsAlgebraic K t
  intro halg
  have : Algebra.IsAlgebraic K K⟮t⟯ := isAlgebraic_adjoin_simple halg.isIntegral
  have : Algebra.IsAlgebraic K⟮t⟯ F := Algebra.IsAlgebraic.of_finite K⟮t⟯ F
  have hKF : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.trans (R := K) (S := K⟮t⟯) (A := F)
  exact Algebra.transcendental_iff_not_isAlgebraic.mp ‹Algebra.Transcendental K F› hKF

end Exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
end AlgebraicCurves.Differentials.Proofs
end ProofImplementation
