/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Sheaves.RelativeSectionTwist
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range

/-!
# is Invertible section Ideal of range subset
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace S_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset

universe u

namespace SInvSection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsInvertible := by
  let X := pullback c u
  let σ : V ⟶ X := rigSection c u ε
  have hσsnd : σ ≫ pullback.snd c u = 𝟙 V := pullback.lift_snd _ _ _
  have hσfst : σ ≫ pullback.fst c u = u ≫ ε.1 := pullback.lift_fst _ _ _
  let j : pullback (U.ι ≫ c) u ⟶ X :=
    pullback.map (U.ι ≫ c) u c u U.ι (𝟙 V) (𝟙 _)
      (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  have hjfst : j ≫ pullback.fst c u = pullback.fst (U.ι ≫ c) u ≫ U.ι := pullback.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd c u = pullback.snd (U.ι ≫ c) u := by
    simp only [j, pullback.map, pullback.lift_snd, Category.comp_id]
  have hrangej : Set.range j = pullback.fst c u ⁻¹' (U : Set C) := by
    rw [Scheme.Pullback.range_map]
    simp [Scheme.Opens.range_ι]
  let pW := pullback.snd (U.ι ≫ c) u
  have hbaseChange : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 pW :=
    hbaseChange.of_isPullback (IsPullback.of_hasPullback (U.ι ≫ c) u)
      (inferInstance : SmoothOfRelativeDimension 1 (U.ι ≫ c))
  have hrange : Set.range σ ⊆ Set.range j := by
    rw [hrangej]
    rintro _ ⟨v, rfl⟩
    change pullback.fst c u (σ v) ∈ (U : Set C)
    rw [← Scheme.Hom.comp_apply, hσfst, Scheme.Hom.comp_apply]
    exact hεU ⟨u v, rfl⟩
  let σW : V ⟶ pullback (U.ι ≫ c) u := IsOpenImmersion.lift j σ hrange
  have hσW : σW ≫ j = σ := IsOpenImmersion.lift_fac _ _ _
  have hσWsnd : σW ≫ pW = 𝟙 V := by
    change σW ≫ pullback.snd (U.ι ≫ c) u = 𝟙 V
    rw [← hjsnd, ← Category.assoc, hσW, hσsnd]
  have hW : (Scheme.Hom.ker σW).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pW)
    σW hσWsnd
  have : IsClosedImmersion σ := by
    have : IsClosedImmersion (σ ≫ pullback.snd c u) := by rw [hσsnd]; infer_instance
    exact IsClosedImmersion.of_comp σ (pullback.snd c u)
  have hcomap : (Scheme.Hom.ker σ).comap j = Scheme.Hom.ker σW := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion σ j]
    let φ : V ⟶ pullback j σ := pullback.lift σW (𝟙 V) (by rw [hσW, Category.id_comp])
    have hφfst : φ ≫ pullback.fst j σ = σW := pullback.lift_fst _ _ _
    have hφsnd : φ ≫ pullback.snd j σ = 𝟙 V := pullback.lift_snd _ _ _
    have : IsIso (pullback.snd j σ) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (top_le_iff.mp fun v _ => ?_)
      exact ⟨φ v, by rw [← Scheme.Hom.comp_apply, hφsnd]; rfl⟩
    have : IsIso φ := by
      have : φ = inv (pullback.snd j σ) := by
        rw [← cancel_mono (pullback.snd j σ), hφsnd, IsIso.inv_hom_id]
      rw [this]; infer_instance
    rw [← hφfst, Scheme.Hom.ker_comp_of_isIso]
  have hsupp : ((Scheme.Hom.ker σ).support : Set ↥X) ⊆ Set.range j := by
    intro x hx
    apply hrange
    rwa [Scheme.Hom.support_ker, (Scheme.Hom.isClosedEmbedding σ).isClosed_range.closure_eq] at hx
  change (Scheme.Hom.ker σ).IsInvertible
  exact Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range j _ hsupp (hcomap ▸ hW)

end SInvSection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra in
theorem _root_.AlgebraicGeometry.RelPicard.isInvertible_sectionIdeal_of_range_subset
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsInvertible :=
  SInvSection.main c ε U hεU u
end S_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
end JacobianVarieties.Picard.Proofs
end ProofImplementation
