/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Tactic.Set

/-!
# Formally Unramified eq of comp eq of is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.FormallyUnramified_eq_of_comp_eq_of_isLocalRing

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.FormallyUnramified.eq_of_comp_eq_of_isLocalRing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    {O : Type u} [CommRing O] [IsLocalRing O]
    (a b : Spec (CommRingCat.of O) ⟶ X) (hf : a ≫ f = b ≫ f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of O))
    (ht : IsLocalRing.closedPoint O ∈ Set.range t.base)
    (hab : t ≫ a = t ≫ b) : a = b := by
  set c : Spec (CommRingCat.of O) ⟶ pullback f f := pullback.lift a b hf with hc
  set E := pullback c (pullback.diagonal f)
  have hE : IsOpenImmersion (pullback.fst c (pullback.diagonal f)) := inferInstance
  have htc : t ≫ c = (t ≫ a) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · rw [Category.assoc, hc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [Category.assoc, hc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, hab]
  have hrange : Set.range (pullback.fst c (pullback.diagonal f)).base = Set.univ := by
    obtain ⟨t₀, ht₀⟩ := ht
    have hmem : IsLocalRing.closedPoint O ∈ Set.range (pullback.fst c (pullback.diagonal f)).base
      := by
      refine ⟨(pullback.lift t (t ≫ a) htc).base t₀, ?_⟩
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, ht₀]
    apply Set.eq_univ_of_forall
    intro x
    exact (IsLocalRing.specializes_closedPoint x).mem_open
      (pullback.fst c (pullback.diagonal f)).isOpenEmbedding.isOpen_range hmem
  have hepi : Epi (pullback.fst c (pullback.diagonal f)).base := by
    rw [TopCat.epi_iff_surjective]
    exact Set.range_eq_univ.mp hrange
  have hiso : IsIso (pullback.fst c (pullback.diagonal f)) := IsOpenImmersion.isIso _
  have hfac : c = (inv (pullback.fst c (pullback.diagonal f)) ≫ pullback.snd c (pullback.diagonal
    f)) ≫
      pullback.diagonal f := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have ha : a = inv (pullback.fst c (pullback.diagonal f)) ≫ pullback.snd c (pullback.diagonal f)
    := by
    have := congrArg (· ≫ pullback.fst f f) hfac
    simp only [hc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      at this
    exact this
  have hb : b = inv (pullback.fst c (pullback.diagonal f)) ≫ pullback.snd c (pullback.diagonal f)
    := by
    have := congrArg (· ≫ pullback.snd f f) hfac
    simp only [hc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id]
      at this
    exact this
  rw [ha, hb]

end AlgebraicCurves.Geometry.Schemes.Proofs.FormallyUnramified_eq_of_comp_eq_of_isLocalRing
end ProofImplementation
