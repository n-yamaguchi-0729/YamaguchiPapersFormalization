/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.UnpointedDescent
import Nyll.AlgebraicCurves.Geometry.Picard.UnrigidifiedGroup
import Nyll.AlgebraicCurves.Geometry.Descent.GroupOfMatching
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The group law on an unpointed Picard descent

The group law comes from the actual tensor-product group of unrigidified classes,
using the proved equivalence between descended scheme points and matching local
classes. No group law or comparison is assumed on the descended carrier.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

noncomputable section

namespace JacobianVarieties.Picard.Unpointed

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
  (L : Type u) [Field L] [Algebra K L]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L))
  {D : RelativePic0Designation L (baseChange K c L)}
  (h : RepresentsRelSubPic (baseChange K c L) ε (algEquivZeroCut (baseChange K c L) ε) D)
  {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of K))
  (e : pullback p (specMap K L) ≅ D.P)
  (he : e.hom ≫ D.toBase = pullback.snd p (specMap K L))
  (hc : DescentAction.eRel (specMap K L) D.toBase p e he ≫ (descentAction c L ε h).act =
    (DescentAction.canonical (specMap K L) p).act ≫ e.hom)

/-- The actual relative group law on the same descended Picard carrier. -/
def groupLawOfPicardDescent : RelativeGroupLaw K p :=
  DescentAction.relativeGroupLawOfMatching (specMap K L) (Unrigidified.zeroCommGrpPresheaf c)
    D.toBase (representableByRestrict c L ε h) p e he hc

theorem groupLawOfPicardDescent_commutative :
    (groupLawOfPicardDescent c L ε h p e he hc).IsCommutative :=
  DescentAction.relativeGroupLawOfMatching_commutative
    (specMap K L) (Unrigidified.zeroCommGrpPresheaf c)
    D.toBase (representableByRestrict c L ε h) p e he hc

end JacobianVarieties.Picard.Unpointed
