/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.FunctionFields.FiniteDimensional_adjoin_of_transcendental
import Mathlib.RingTheory.Unramified.Finite

/-!
# Is Curve Over finite Dimensional adjoin simple of transcendental of ess Finite Type
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs
namespace IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType

open AlgebraicCurve IntermediateField

namespace R1AF8KappaFinChild

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem subsingleton_kaehler_adjoin (x : F)
    (hspan : Submodule.span F {KaehlerDifferential.D K F x} = ⊤) :
    Subsingleton Ω[F⁄K⟮x⟯] := by
  have hx : (x : F) ∈ K⟮x⟯ := mem_adjoin_simple_self K x
  have hDx : KaehlerDifferential.map K K⟮x⟯ F F (KaehlerDifferential.D K F x) = 0 := by
    rw [KaehlerDifferential.map_D]
    have : (algebraMap F F x) = algebraMap K⟮x⟯ F ⟨x, hx⟩ := rfl
    rw [this, Derivation.map_algebraMap]
  have hmap0 : KaehlerDifferential.map K K⟮x⟯ F F = 0 := by
    apply LinearMap.ext
    intro ω
    have hω : ω ∈ Submodule.span F {KaehlerDifferential.D K F x} := by rw [hspan]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hω
    rw [LinearMap.map_smul, hDx, smul_zero, LinearMap.zero_apply]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := KaehlerDifferential.map_surjective K K⟮x⟯ F a
  obtain ⟨b', rfl⟩ := KaehlerDifferential.map_surjective K K⟮x⟯ F b
  rw [hmap0, LinearMap.zero_apply, LinearMap.zero_apply]

theorem exists_finiteDimensional_adjoin [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ x : F, FiniteDimensional K⟮x⟯ F := by
  obtain ⟨hfree, hrank⟩ := (IsCurveOver.kaehler_free_rank_one (K := K) (F := F))
  have := hfree
  have : Module.Finite F Ω[F⁄K] := Module.finite_of_finrank_eq_succ hrank
  obtain ⟨x, hx⟩ : ∃ x : F, KaehlerDifferential.D K F x ≠ 0 := by
    by_contra! h
    have htop := KaehlerDifferential.span_range_derivation (R := K) (S := F)
    have hbot : Submodule.span F (Set.range (KaehlerDifferential.D K F)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨y, rfl⟩
      exact h y
    rw [hbot] at htop
    have hsub : Subsingleton Ω[F⁄K] := (Submodule.subsingleton_iff F).mp
      (subsingleton_of_bot_eq_top htop)
    have : Module.finrank F Ω[F⁄K] = 0 := Module.finrank_zero_of_subsingleton
    omega
  have hspan : Submodule.span F {KaehlerDifferential.D K F x} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrank, finrank_span_singleton hx]
  refine ⟨x, ?_⟩
  have : Subsingleton Ω[F⁄K⟮x⟯] := subsingleton_kaehler_adjoin x hspan
  have : Algebra.FormallyUnramified K⟮x⟯ F := ⟨inferInstance⟩
  have : Algebra.EssFiniteType K⟮x⟯ F := Algebra.EssFiniteType.of_comp K K⟮x⟯ F
  exact Algebra.FormallyUnramified.finite_of_free (R := K⟮x⟯) (S := F)

end R1AF8KappaFinChild

end IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
end AlgebraicCurves.FunctionFields.Proofs

namespace AlgebraicCurve.IsCurveOver



open _root_.AlgebraicCurves.FunctionFields.Proofs in
open IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType in
open AlgebraicCurve IntermediateField in
theorem finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    {t : F} (ht : Transcendental K t) :
    FiniteDimensional K⟮t⟯ F := by
  obtain ⟨x, hx⟩ := R1AF8KappaFinChild.exists_finiteDimensional_adjoin (K := K) (F := F)
  have := hx
  exact AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x ht
end AlgebraicCurve.IsCurveOver
end ProofImplementation
