/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# The actual finite étale extension supplied by normalization

When the relative normalization of a finite étale cover of an open subscheme
is finite étale, it is an extension of the original cover. The restriction
isomorphism comes from the actual open pullback and normalization comparison,
using that a finite cover is already its own relative normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Finite étale relative normalization gives an actual extending object,
together with an isomorphism from its restriction to the original cover. -/
theorem exists_finiteEtale_extension_of_normalization
    {X : Scheme.{u}} (U : X.Opens) [QuasiCompact U.ι]
    (W : FiniteEtale U)
    [IsFiniteEtale (W.hom ≫ U.ι).fromNormalization] :
    ∃ V : FiniteEtale X, Nonempty ((FiniteEtale.pullback U.ι).obj V ≅ W) := by
  let F : W.left ⟶ X := W.hom ≫ U.ι
  let g : W.left ⟶ U := W.hom
  let V : FiniteEtale X := FiniteEtale.mk F.fromNormalization
  have H : IsPullback (𝟙 W.left) g F U.ι :=
    IsPullback.of_horiz_isIso_mono ⟨Category.id_comp F⟩
  let e : pullback F U.ι ≅ W.left :=
    (IsPullback.of_hasPullback F U.ι).isoIsPullback _ _ H
  have he : e.hom ≫ g = pullback.snd F U.ι :=
    IsPullback.isoIsPullback_hom_snd W.left U
      (IsPullback.of_hasPullback F U.ι) H
  let en := normalizationSourceIso (pullback.snd F U.ι) g e he
  have hen : en.inv ≫ (pullback.snd F U.ι).fromNormalization = g.fromNormalization :=
    (Iso.inv_comp_eq en).mpr (normalizationSourceIso_hom_fromNormalization _ _ _ _).symm
  let eN : W.left ≅ pullback F.fromNormalization U.ι :=
    asIso g.toNormalization ≪≫ en.symm ≪≫ asIso (F.normalizationPullback U.ι)
  have heN : eN.hom ≫ pullback.snd F.fromNormalization U.ι = g := by
    change (g.toNormalization ≫ en.inv ≫ F.normalizationPullback U.ι) ≫
      pullback.snd F.fromNormalization U.ι = g
    rw [Category.assoc, Category.assoc, Scheme.Hom.normalizationPullback_snd,
      hen, Scheme.Hom.toNormalization_fromNormalization]
  refine ⟨V, ⟨?_⟩⟩
  exact MorphismProperty.Over.isoMk eN.symm ((Iso.inv_comp_eq eN).mpr heN.symm)

end EtaleFundamentalGroups.Inertia
