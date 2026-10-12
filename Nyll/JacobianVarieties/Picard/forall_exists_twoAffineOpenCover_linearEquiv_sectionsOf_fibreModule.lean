/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

/-!
# Cohomology of two presentations of a fibre

The canonical pullback comparison transports two-affine-open covers and identifies the zeroth
and first cohomology of the associated fibre modules in both directions.
-/

section ProofImplementation

namespace AlgebraicGeometry.RelPicard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hx : s ≫ t = x) (M : (pullback c t).Modules) :
    (∀ 𝒱 : (pullback c x).TwoAffineOpenCover,
      ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback
            (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback
            (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H1)) ∧
    (∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      ∃ 𝒱 : (pullback c x).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback
            (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback
            (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H1)) := by
  subst hx
  let φ : pullback (pullback.snd c t) s ≅ pullback c (s ≫ t) := pullbackLeftPullbackSndIso c t s
  have h1 : φ.hom ≫ pullback.snd c (s ≫ t) = fibreAt c t s := by
    exact pullbackLeftPullbackSndIso_hom_snd c t s
  have h3 : φ.hom ≫ baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t) =
      pullback.fst (pullback.snd c t) s := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      erw [pullback.lift_fst]
      rw [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    · rw [Category.assoc]
      erw [pullback.lift_snd]
      rw [← Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.condition]
  let N : (pullback c (s ≫ t)).Modules :=
    (Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M
  have e : fibreModule c t s M ≅ (Scheme.Modules.pullback φ.hom).obj N :=
    (Scheme.Modules.pullbackCongr h3.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp φ.hom
        (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).app M).symm
  have h1' : φ.inv ≫ fibreAt c t s = pullback.snd c (s ≫ t) := by
    rw [← h1, Iso.inv_hom_id_assoc]
  have e' : N ≅ (Scheme.Modules.pullback φ.inv).obj (fibreModule c t s M) :=
    ((Scheme.Modules.pullback φ.inv).mapIso e ≪≫
      (Scheme.Modules.pullbackComp φ.inv φ.hom).app N ≪≫
      (Scheme.Modules.pullbackCongr φ.inv_hom_id).app N ≪≫
      (Scheme.Modules.pullbackId (pullback c (s ≫ t))).app N).symm
  refine ⟨fun 𝒱' => ?_, fun 𝒲 => ?_⟩
  · obtain ⟨𝒱, -, -, ⟨l0⟩, ⟨l1⟩⟩ :=
      Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
        (fibreAt c t s) (pullback.snd c (s ≫ t)) φ h1 𝒱' N
        (fibreModule c t s M) e
    exact ⟨𝒱, ⟨l0⟩, ⟨l1⟩⟩
  · obtain ⟨𝒱, -, -, ⟨l0⟩, ⟨l1⟩⟩ :=
      Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
        (pullback.snd c (s ≫ t)) (fibreAt c t s) φ.symm h1' 𝒲
        (fibreModule c t s M) N e'
    exact ⟨𝒱, ⟨l0.symm⟩, ⟨l1.symm⟩⟩
end AlgebraicGeometry.RelPicard
end ProofImplementation
