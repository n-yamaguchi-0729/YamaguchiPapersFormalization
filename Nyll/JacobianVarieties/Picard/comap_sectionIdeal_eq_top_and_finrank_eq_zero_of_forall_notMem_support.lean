/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Maps.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier

/-!
# A section ideal away from the support

A section disjoint from the support of an ideal pulls back to the unit ideal on its subscheme.
The resulting empty subscheme has finite rank zero.
-/

section ProofImplementation

namespace AlgebraicGeometry.RelPicard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k : Type u} [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (J : (pullback c t).IdealSheafData)
    (hJ : ∀ x ∈ Set.range (rigSection c t σ), x ∉ J.support) :
    (sectionIdeal c σ t).comap J.subschemeι = ⊤ ∧
      ((sectionIdeal c σ t).comap J.subschemeι).IsInvertible ∧
      IsFinite (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫
        J.subschemeι ≫ pullback.snd c t) ∧
      ∀ q : Spec (CommRingCat.of k),
        (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫
          J.subschemeι ≫ pullback.snd c t).finrank q =
          0 := by
  have hs_snd : rigSection c t σ ≫ pullback.snd c t = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion (rigSection c t σ) := by
    have : IsClosedImmersion (rigSection c t σ ≫ pullback.snd c t) := by
      rw [hs_snd]
      infer_instance
    exact IsClosedImmersion.of_comp (rigSection c t σ) (pullback.snd c t)
  have hIker : sectionIdeal c σ t = (rigSection c t σ).ker := rfl
  have hsupp : ((sectionIdeal c σ t).support : Set ↥(pullback c t)) =
      Set.range (rigSection c t σ) := by
    rw [hIker, Scheme.Hom.support_ker,
      (Scheme.Hom.isClosedEmbedding (rigSection c t σ)).isClosed_range.closure_eq]
  have hK : (sectionIdeal c σ t).comap J.subschemeι = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    refine le_bot_iff.mp fun w hw => ?_
    have hw' : J.subschemeι w ∈ ((sectionIdeal c σ t).support : Set ↥(pullback c t)) := hw
    rw [hsupp] at hw'
    refine (hJ _ hw' ?_).elim
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [hK]
  refine ⟨rfl, Scheme.IdealSheafData.isInvertible_top, inferInstance, fun q => ?_⟩
  generalize ((⊤ : (J.subscheme).IdealSheafData).subschemeι ≫ J.subschemeι ≫ pullback.snd c t) = g
  have : IsOpenImmersion g := isOpenImmersion_of_isEmpty g
  have hns : ¬ Surjective g := fun h => by
    obtain ⟨x, -⟩ := h.surj q
    exact isEmptyElim x
  rw [← Scheme.Hom.one_le_finrank_iff_surjective] at hns
  simp only [Pi.le_def, Pi.one_apply, not_forall, not_le, Nat.lt_one_iff] at hns
  obtain ⟨y, hy⟩ := hns
  rwa [Subsingleton.elim q y]
end AlgebraicGeometry.RelPicard
end ProofImplementation
