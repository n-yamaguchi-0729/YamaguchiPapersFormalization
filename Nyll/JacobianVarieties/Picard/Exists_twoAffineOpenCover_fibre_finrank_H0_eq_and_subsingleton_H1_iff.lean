/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Mathlib.Util.WithWeakNamespace

/-!
# Relative Picard varieties and fibre cohomology

Compare fibre zeroth cohomology and vanishing of first cohomology after extending the residue
field.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace Exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

open Exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (F : (pullback c t).Modules)
    (hF : Scheme.Modules.IsInvertible F)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) (K : Type u) [Field K] [Algebra k K] :
    ∃ 𝒲' : (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫
      s)).TwoAffineOpenCover,
      Module.finrank K (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
        (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H0 =
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 ∧
      (Subsingleton (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
        (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H1 ↔
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1) := by
  have hM : Scheme.Modules.IsInvertible (fibreModule c t s F) := hF.pullback _
  obtain ⟨h0, h1⟩ :=
    Scheme.TwoAffineOpenCover.finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
    (fibreAt c t s) 𝒲 (fibreModule c t s F) hM.1 K
  let ψ : pullback (pullback.snd (pullback.snd c t) s) (Scheme.TwoAffineOpenCover.specMap k K) ≅
    pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s) :=
    pullbackLeftPullbackSndIso (pullback.snd c t) s (Scheme.TwoAffineOpenCover.specMap k K)
  let φ : pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s) ≅ pullback
    (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K) := ψ.symm
  have hφx : φ.hom ≫ pullback.snd (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K) =
    fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) := by
    change ψ.inv ≫ pullback.snd (pullback.snd (pullback.snd c t) s)
      (Scheme.TwoAffineOpenCover.specMap k K) =
      pullback.snd (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd _ _ _).symm
  have hφfst : φ.hom ≫ pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K) ≫
    pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s) := by
    change ψ.inv ≫ pullback.fst (pullback.snd (pullback.snd c t) s)
      (Scheme.TwoAffineOpenCover.specMap k K) ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_fst _ _ _).symm
  let e : fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F ≅
    (Scheme.Modules.pullback φ.hom).obj
      ((Scheme.Modules.pullback (pullback.fst (fibreAt c t s)
        (Scheme.TwoAffineOpenCover.specMap k K))).obj (fibreModule c t s F)) :=
    ((Scheme.Modules.pullbackCongr hφfst).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp (φ.hom ≫ pullback.fst (fibreAt c t s)
        (Scheme.TwoAffineOpenCover.specMap k K)) (pullback.fst (pullback.snd c t) s)).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp φ.hom (pullback.fst (fibreAt c t s)
        (Scheme.TwoAffineOpenCover.specMap k K))).app _).symm
  obtain ⟨𝒲', -, -, ⟨f0⟩, ⟨f1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s)) (pullback.snd (fibreAt c t s)
      (Scheme.TwoAffineOpenCover.specMap k K)) φ hφx
    (𝒲.pullback (fibreAt c t s) K) _ _ e
  exact ⟨𝒲', f0.finrank_eq.trans h0, f1.toEquiv.subsingleton_congr.trans h1⟩
end Exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
end JacobianVarieties.Picard.Proofs
end ProofImplementation
