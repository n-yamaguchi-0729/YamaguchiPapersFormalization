/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationStalkLocalization
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Relative normalization at a point inside the original open

At a point of the open, the map from the spectrum of the stalk factors
through that open. The original finite etale cover is therefore already
integral after base change, so its relative normalization is itself.
The actual normalization-localization comparison returns the assertion for
the original normalization's base change.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Inside the original open, the relative normalization of a finite etale
cover has finite etale base change to the actual ambient stalk. -/
theorem finiteEtale_normalization_stalk_of_mem_open
    {X : Scheme.{u}} (U : X.Opens) [QuasiCompact U.ι]
    (W : FiniteEtale U) (x : X) (hx : x ∈ U) :
    IsFiniteEtale (pullback.snd (W.hom ≫ U.ι).fromNormalization (X.fromSpecStalk x)) := by
  let c := U.fromSpecStalkOfMem x hx
  let b := X.fromSpecStalk x
  let F := W.hom ≫ U.ι
  let g := pullback.snd W.hom c
  have Hc : IsPullback c (𝟙 _) U.ι b :=
    IsPullback.of_vert_isIso_mono ⟨by
      rw [Category.id_comp]
      exact U.fromSpecStalkOfMem_ι x hx⟩
  have H : IsPullback (pullback.fst W.hom c) g F b := by
    simpa only [Category.comp_id] using (IsPullback.of_hasPullback W.hom c).paste_vert Hc
  let e := (IsPullback.of_hasPullback F b).isoIsPullback _ _ H
  have he : e.hom ≫ g = pullback.snd F b :=
    IsPullback.isoIsPullback_hom_snd W.left (Spec (X.presheaf.stalk x))
      (IsPullback.of_hasPullback F b) H
  let : IsFinite (pullback.snd F b) := by
    rw [← he]
    infer_instance
  let : Etale (pullback.snd F b) := by
    rw [← he]
    infer_instance
  let f := pullback.snd F b
  have hf : f.fromNormalization = inv f.toNormalization ≫ f := by
    exact (IsIso.inv_hom_id_assoc f.toNormalization f.fromNormalization).symm.trans
      (congrArg (fun k => inv f.toNormalization ≫ k)
        (Scheme.Hom.toNormalization_fromNormalization f))
  let : IsFinite f.fromNormalization := by
    rw [hf]
    infer_instance
  let : Etale f.fromNormalization := by
    rw [hf]
    infer_instance
  let : IsIso (F.normalizationPullback b) := isIso_normalizationPullback_fromSpecStalk F x
  have hb : pullback.snd F.fromNormalization b =
      inv (F.normalizationPullback b) ≫ f.fromNormalization := by
    exact (IsIso.inv_hom_id_assoc (F.normalizationPullback b)
      (pullback.snd F.fromNormalization b)).symm.trans
        (congrArg (fun k => inv (F.normalizationPullback b) ≫ k)
          (Scheme.Hom.normalizationPullback_snd F b))
  change IsFiniteEtale (pullback.snd F.fromNormalization b)
  rw [hb]
  exact ⟨⟩

end EtaleFundamentalGroups.Inertia
