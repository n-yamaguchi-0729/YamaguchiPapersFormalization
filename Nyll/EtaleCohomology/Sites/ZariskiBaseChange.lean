/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Sites.ZariskiRestriction
import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.SetSheafFunctors
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.Topology.Sheaves.Functors

/-!
# Zariski restriction and actual étale base change

The cartesian square of an open subscheme and its inverse image compares
the existing small-site base change with the inverse-image functor on opens.
It induces the direct-image comparison on sheaves. Its adjunction mate is
the actual map from topological inverse image to restricted étale inverse
image, with the corresponding equality of the chosen adjunction units.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private def zariskiBaseChangeObjIso (U : Y.Opens) :
    (etaleBaseChange f).obj ((zariskiToEtale Y).obj U) ≅
      (zariskiToEtale X).obj ((Opens.map f.base).obj U) := by
  let e : Limits.pullback U.ι f ≅ (f ⁻¹ᵁ U).toScheme :=
    (isPullback_morphismRestrict f U).isoPullback.symm
  exact MorphismProperty.Over.isoMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) e
    (isPullback_morphismRestrict f U).isoPullback_inv_snd

/-- The actual pullback of an open subscheme is its inverse-image open. -/
def zariskiToEtaleBaseChangeIso :
    zariskiToEtale Y ⋙ etaleBaseChange f ≅
      Opens.map f.base ⋙ zariskiToEtale X := by
  refine NatIso.ofComponents (zariskiBaseChangeObjIso f) ?_
  intro U V g
  apply ((etaleOpenImageAdjunction X).homEquiv
    ((etaleBaseChange f).obj ((zariskiToEtale Y).obj U))
    ((Opens.map f.base).obj V)).symm.injective
  exact Subsingleton.elim _ _

variable (A : Type v) [Category.{w} A]

/-- Restricting étale direct image to opens agrees with topological direct
image of the restricted sheaf. -/
def etaleZariskiPushforwardIso :
    (etaleBaseChange f).sheafPushforwardContinuous A
        Y.smallEtaleTopology X.smallEtaleTopology ⋙ etaleZariskiRestriction Y A ≅
      etaleZariskiRestriction X A ⋙ TopCat.Sheaf.pushforward A f.base := by
  let : (Opens.map f.base ⋙ zariskiToEtale X).IsContinuous
      (Opens.grothendieckTopology Y) X.smallEtaleTopology :=
    Functor.isContinuous_comp (Opens.map f.base) (zariskiToEtale X)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) X.smallEtaleTopology
  exact Functor.sheafPushforwardContinuousComp' (zariskiToEtaleBaseChangeIso f) A
      (Opens.grothendieckTopology Y) Y.smallEtaleTopology X.smallEtaleTopology ≪≫
    (Functor.sheafPushforwardContinuousComp (Opens.map f.base) (zariskiToEtale X) A
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      X.smallEtaleTopology).symm

/-- The canonical map from topological inverse image to the Zariski
restriction of actual set-valued étale inverse image. -/
def etaleZariskiSetPullbackComparison :
    etaleZariskiRestriction Y (Type u) ⋙ TopCat.Sheaf.pullback (Type u) f.base ⟶
      etaleSetPullback f ⋙ etaleZariskiRestriction X (Type u) :=
  ((mateEquiv (etaleSetPullbackPushforwardAdjunction f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.base)).symm
      (etaleZariskiPushforwardIso f (Type u)).hom).natTrans

/-- The comparison identifies the actual étale adjunction unit with the
topological adjunction unit followed by the constructed comparison. -/
lemma etaleZariskiSetPullbackComparison_unit
    (F : Sheaf Y.smallEtaleTopology (Type u)) :
    (etaleZariskiRestriction Y (Type u)).map
        ((etaleSetPullbackPushforwardAdjunction f).unit.app F) ≫
      (etaleZariskiPushforwardIso f (Type u)).hom.app ((etaleSetPullback f).obj F) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.base).unit.app
        ((etaleZariskiRestriction Y (Type u)).obj F) ≫
      (TopCat.Sheaf.pushforward (Type u) f.base).map
        ((etaleZariskiSetPullbackComparison f).app F) :=
  unit_mateEquiv_symm (etaleSetPullbackPushforwardAdjunction f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.base)
    (etaleZariskiPushforwardIso f (Type u)).hom F

end EtaleCohomology
