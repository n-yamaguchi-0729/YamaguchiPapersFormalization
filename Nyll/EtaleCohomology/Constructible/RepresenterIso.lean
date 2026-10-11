/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.SchemeTheory.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Yoneda

/-!
# Transporting finite étale representers across a scheme isomorphism

A finite étale representative of the restriction along an isomorphism gives
a representative of the original sheaf. We use its base change along the
inverse isomorphism, the map/pullback adjunction, and the natural comparison
between composing the two isomorphisms and the identity functor.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleCohomology

/-- Pulling the finite étale representer back along the inverse isomorphism
represents the original sheaf. The comparison is constructed from the actual
postcomposition/base-change adjunction and its natural identity comparison. -/
def finiteEtaleRepresentableBy_of_isoRestriction {X Y : Scheme.{u}} (e : Y ≅ X)
    (G : Sheaf X.smallEtaleTopology (Type u)) (W : FiniteEtale Y)
    (h : ((etalePostcompose e.hom).op ⋙ G.obj).RepresentableBy
      ((finiteEtaleToEtale Y).obj W)) :
    G.obj.RepresentableBy ((finiteEtaleToEtale X).obj ((FiniteEtale.pullback e.inv).obj W)) := by
  let c : etalePostcompose e.inv ⋙ etalePostcompose e.hom ≅ 𝟭 X.Etale :=
    (MorphismProperty.Over.mapComp (P := show MorphismProperty Scheme.{u} from @Etale) ⊤
      (show Etale e.inv from inferInstance) (show Etale e.hom from inferInstance)
      (𝟙 X) e.inv_hom_id.symm).symm ≪≫
    MorphismProperty.Over.mapId (P := show MorphismProperty Scheme.{u} from @Etale) ⊤ X
  let r := ((etalePostcomposeBaseChangeAdjunction e.inv).representableBy
    ((finiteEtaleToEtale Y).obj W)).ofIso
      (Functor.isoWhiskerLeft (etalePostcompose e.inv).op h.toIso)
  exact r.ofIso ((Functor.isoWhiskerRight (NatIso.op c.symm) G.obj) ≪≫ G.obj.leftUnitor)

end EtaleCohomology
