/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import EtaleCohomology.Sites.ZariskiBaseChange
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Topology.Sheaves.Functors

/-!
# Underlying Zariski sets of module-valued étale inverse image

Forgetting modules and restricting to opens gives an actual sheaf of sets.
Direct image commutes with these operations. Taking mates compares its
topological inverse image with the underlying Zariski sheaf of module-valued
étale inverse image, including the actual chosen adjunction units.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace EtaleCohomology

local instance moduleForget_hasSheafCompose {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    J.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
  let : Limits.PreservesLimitsOfSize.{w, max v w} (forget (ModuleCat.{u} Λ)) :=
    (ModuleCat.adj Λ).rightAdjoint_preservesLimits
  exact hasSheafCompose_of_preservesLimitsOfSize
    (F := forget (ModuleCat.{u} Λ)) J

/-- The underlying sheaf of sets on the actual Zariski opens of the scheme. -/
def etaleModuleZariskiRestriction (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf (Opens.grothendieckTopology X) (Type u) :=
  sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u} Λ)) ⋙
    etaleZariskiRestriction X (Type u)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u) [CommRing Λ]

/-- The underlying Zariski sheaf of module direct image is its actual
topological direct image. -/
def etaleModuleZariskiPushforwardIso :
    etalePushforward f Λ ⋙ etaleModuleZariskiRestriction Y Λ ≅
      etaleModuleZariskiRestriction X Λ ⋙ TopCat.Sheaf.pushforward (Type u) f.base :=
  Functor.isoWhiskerLeft (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u} Λ)))
    (etaleZariskiPushforwardIso f (Type u))

/-- The canonical mixed comparison from topological set inverse image to
the underlying Zariski sheaf of module-valued étale inverse image. -/
def etaleModuleZariskiPullbackComparison :
    etaleModuleZariskiRestriction Y Λ ⋙ TopCat.Sheaf.pullback (Type u) f.base ⟶
      etalePullback f Λ ⋙ etaleModuleZariskiRestriction X Λ :=
  ((mateEquiv (etalePullbackPushforwardAdjunction f Λ)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.base)).symm
      (etaleModuleZariskiPushforwardIso f Λ).hom).natTrans

/-- The mixed comparison carries the actual topological unit to the
underlying actual module-valued étale unit. -/
lemma etaleModuleZariskiPullbackComparison_unit
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleModuleZariskiRestriction Y Λ).map
        ((etalePullbackPushforwardAdjunction f Λ).unit.app F) ≫
      (etaleModuleZariskiPushforwardIso f Λ).hom.app ((etalePullback f Λ).obj F) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.base).unit.app
        ((etaleModuleZariskiRestriction Y Λ).obj F) ≫
      (TopCat.Sheaf.pushforward (Type u) f.base).map
        ((etaleModuleZariskiPullbackComparison f Λ).app F) :=
  unit_mateEquiv_symm (etalePullbackPushforwardAdjunction f Λ)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.base)
    (etaleModuleZariskiPushforwardIso f Λ).hom F

end EtaleCohomology
