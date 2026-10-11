/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_dense_range_isPullback_lift_specMap_comp_point.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Curve Model dense range is Pullback lift spec Map comp point
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_dense_range_isPullback_lift_specMap_comp_point

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem _root_.AlgebraicCurve.CurveModel.dense_range_isPullback_lift_specMap_comp_point
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type u} [Field L] [Algebra K L] (M : CurveModel K L)
    (C : Type u) [Field C] (cK : K →+* C)
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ M.C) (t : Y ⟶ Spec (CommRingCat.of C))
    (hY : IsPullback g t M.toBase (Spec.map (CommRingCat.ofHom cK))) :
    Dense (Set.range fun p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} =>
      (hY.lift (Spec.map (CommRingCat.ofHom cK) ≫ p.1) (𝟙 _)
        (by rw [Category.assoc, p.2, Category.comp_id, Category.id_comp])).base
        (IsLocalRing.closedPoint C)) := by
  classical
  rw [dense_iff_inter_open]
  rintro V hVo ⟨y₀, hy₀⟩
  have : UniversallyOpen (Spec.map (CommRingCat.ofHom cK)) := inferInstance
  have : UniversallyOpen g := MorphismProperty.of_isPullback hY.flip inferInstance
  have hgV : IsOpen (g.base '' V) := g.isOpenMap _ hVo
  have : JacobsonSpace ↥M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  have hdense : Dense (closedPoints ↥M.C) := by
    rw [dense_iff_closure_eq]; exact closure_closedPoints
  obtain ⟨_, ⟨y, hyV, rfl⟩, hx⟩ := hdense.inter_open_nonempty _ hgV ⟨g.base y₀, y₀, hy₀, rfl⟩
  set p : Spec (CommRingCat.of K) ⟶ M.C := pointOfClosedPoint M.toBase (g.base y) hx with hp
  have hpb : p ≫ M.toBase = 𝟙 _ := pointOfClosedPoint_comp M.toBase (g.base y) hx
  have key : ∀ hw, (hY.lift (Spec.map (CommRingCat.ofHom cK) ≫ p) (𝟙 _) hw).base
    (IsLocalRing.closedPoint C) = y := by
    intro hw
    have hee : Spec.map (residueFieldIsoBase M.toBase (g.base y) hx).inv ≫ Spec.map
      (residueFieldIsoBase M.toBase (g.base y) hx).hom = 𝟙 _ := by
      rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
    have hfac : Y.fromSpecResidueField y ≫ g = (Spec.map (g.residueFieldMap y) ≫ Spec.map
      (residueFieldIsoBase M.toBase (g.base y) hx).inv) ≫ p := by
      rw [hp]
      dsimp only [pointOfClosedPoint]
      simp only [Category.assoc, ← Category.assoc
        (Spec.map (residueFieldIsoBase M.toBase (g.base y) hx).inv), hee,
        Category.id_comp, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    have hιz : Y.fromSpecResidueField y =
        (Y.fromSpecResidueField y ≫ t) ≫ hY.lift (Spec.map (CommRingCat.ofHom cK) ≫ p) (𝟙 _) hw :=
          by
      apply hY.hom_ext
      · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc]
        have : (Y.fromSpecResidueField y ≫ t) ≫ Spec.map (CommRingCat.ofHom cK) =
            Spec.map (g.residueFieldMap y) ≫ Spec.map (residueFieldIsoBase M.toBase (g.base y)
              hx).inv := by
          rw [Category.assoc, ← hY.w, ← Category.assoc, hfac, Category.assoc, hpb, Category.comp_id]
        rw [this, hfac]
      · rw [Category.assoc, IsPullback.lift_snd, Category.comp_id]
    have h1 : (Y.fromSpecResidueField y).base (IsLocalRing.closedPoint (Y.residueField y)) = y :=
      Scheme.fromSpecResidueField_apply y _
    conv_rhs => rw [← h1, hιz]
    calc
      _ = (hY.lift (Spec.map (CommRingCat.ofHom cK) ≫ p) (𝟙 _) hw).base
          ((Y.fromSpecResidueField y ≫ t).base (IsLocalRing.closedPoint (Y.residueField y))) := by
            congr 1
            exact Subsingleton.elim _ _
      _ = _ := (Scheme.Hom.comp_apply _ _ _).symm
  refine ⟨_, ?_, ⟨⟨p, hpb⟩, rfl⟩⟩
  dsimp only
  rw [key]
  exact hyV
end AlgebraicCurves.Models.Proofs.CurveModel_dense_range_isPullback_lift_specMap_comp_point
end ProofImplementation
