/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_irreducibleSpace_and_topologicalKrullDim_pullback_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq

/-!
# Curve Model irreducible Space and topological Krull Dim pullback eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_irreducibleSpace_and_topologicalKrullDim_pullback_eq_one

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem _root_.AlgebraicCurve.CurveModel.irreducibleSpace_and_topologicalKrullDim_pullback_eq_one
    {K₁ : Type} [Field K₁] [IsAlgClosed K₁] {F : Type} [Field F] [Algebra K₁ F]
    (𝔐 : AlgebraicCurve.CurveModel K₁ F)
    {B : Type} [CommRing B] (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (sbar : Spec (CommRingCat.of K₁) ⟶ Spec (CommRingCat.of B))
    (e𝔐 : 𝔐.C ⟶ Limits.pullback πX sbar) [IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ Limits.pullback.snd πX sbar = 𝔐.toBase)
    (k : Type) [Field k] (j : K₁ →+* k) :
    IrreducibleSpace ↑(Limits.pullback πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) ∧
    topologicalKrullDim ↑(Limits.pullback πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) = 1 ∧
    LocallyOfFiniteType (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) ∧
    QuasiCompact (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) := by
  classical
  set y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K₁) := Spec.map (CommRingCat.ofHom j) with
    hy
  have heq : 𝔐.toBase ≫ 𝟙 _ = e𝔐 ≫ pullback.snd πX sbar := by rw [Category.comp_id, he𝔐]
  let m : pullback 𝔐.toBase y ⟶ pullback (pullback.snd πX sbar) y :=
    pullback.map 𝔐.toBase y (pullback.snd πX sbar) y e𝔐 (𝟙 _) (𝟙 _) heq (by simp)
  have : IsIso m := inferInstance
  let e : pullback 𝔐.toBase y ≅ pullback πX (y ≫ sbar) := asIso m ≪≫ pullbackLeftPullbackSndIso πX
    sbar y
  have hm : m ≫ pullback.snd (pullback.snd πX sbar) y = pullback.snd 𝔐.toBase y := by
    change pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_snd, Category.comp_id]
  have hsnd : e.hom ≫ pullback.snd πX (y ≫ sbar) = pullback.snd 𝔐.toBase y := by
    simp only [e, Iso.trans_hom, asIso_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, hm]
  have hsnd' : pullback.snd πX (y ≫ sbar) = e.inv ≫ pullback.snd 𝔐.toBase y := by
    rw [← hsnd, Iso.inv_hom_id_assoc]
  have hGI : GeometricallyIrreducible 𝔐.toBase :=
    AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed 𝔐.toBase
  have : IrreducibleSpace ↑(pullback 𝔐.toBase y) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := pullback.snd 𝔐.toBase y)
  have hsm : SmoothOfRelativeDimension 1 (pullback.snd 𝔐.toBase y) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback 𝔐.toBase y) inferInstance
  have : Smooth 𝔐.toBase := SmoothOfRelativeDimension.smooth (n := 1) (f := 𝔐.toBase)
  have h1 : IrreducibleSpace ↑(pullback πX (y ≫ sbar)) :=
    e.hom.homeomorph.surjective.irreducibleSpace e.hom.homeomorph.continuous
  have h2 : topologicalKrullDim ↑(pullback πX (y ≫ sbar)) = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
    have hpre : ((pullback.snd 𝔐.toBase y).base ⁻¹' {(default : ↥(Spec (CommRingCat.of k)))}) =
      Set.univ := by
      ext x; simp [Subsingleton.elim ((pullback.snd 𝔐.toBase y).base x) default]
    have hne : ((pullback.snd 𝔐.toBase y).base ⁻¹' {(default : ↥(Spec (CommRingCat.of
      k)))}).Nonempty := by
      rw [hpre]; exact Set.univ_nonempty
    have h := AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq
      (pullback.snd 𝔐.toBase y) 1 default hne
    rw [hpre] at h
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ ↑(pullback 𝔐.toBase
      y)).isHomeomorph]
    exact_mod_cast h
  have h3 : LocallyOfFiniteType (pullback.snd πX (y ≫ sbar)) := by rw [hsnd']; infer_instance
  have h4 : QuasiCompact (pullback.snd πX (y ≫ sbar)) := by rw [hsnd']; infer_instance
  exact ⟨h1, h2, h3, h4⟩
end CurveModel_irreducibleSpace_and_topologicalKrullDim_pullback_eq_one
end AlgebraicCurves.Models.Proofs
end ProofImplementation
