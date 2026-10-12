/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.GenericPointNaturality
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1PullbackComposition

/-!
# Actual H¹ pullback at the generic point

Restriction to the function field commutes with dominant scheme pullback.
Both sides use the existing derived-sheaf maps, rather than a replacement
cohomology model or an assumed compatibility square.
-/

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

/-- The actual generic-point square induces the corresponding commutative
square on derived finite-coefficient H¹. -/
theorem finiteH1Pullback_genericPoint
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : DenseRange f)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ Spec (.of X.functionField))
    (A : AddCommGrpCat.{0}) [Finite A]
    (a : Sheaf.H.{0} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1) :
    constantCohomologyPullback (X.fromSpecStalk (genericPoint X)) A 1
        (constantCohomologyPullback f A 1 a) =
      constantCohomologyPullback (Spec.map (CommRingCat.ofHom (f.functionFieldMap hf))) A 1
        (constantCohomologyPullback (Y.fromSpecStalk (genericPoint Y)) A 1 a) := by
  calc
    _ = constantCohomologyPullback (X.fromSpecStalk (genericPoint X) ≫ f) A 1 a :=
      (constantFiniteH1Pullback_comp (X.fromSpecStalk (genericPoint X)) f η A a).symm
    _ = constantCohomologyPullback
        (Spec.map (CommRingCat.ofHom (f.functionFieldMap hf)) ≫
          Y.fromSpecStalk (genericPoint Y)) A 1 a :=
      congrArg (fun q => constantCohomologyPullback q A 1 a)
        (functionFieldMap_genericPoint f hf).symm
    _ = _ := constantFiniteH1Pullback_comp
      (Spec.map (CommRingCat.ofHom (f.functionFieldMap hf)))
      (Y.fromSpecStalk (genericPoint Y)) η A a

end AnabelianGeometry.WeightFiltration
