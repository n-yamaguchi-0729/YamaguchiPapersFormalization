/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
import EtaleFundamentalGroups.GeometricFiber.BasePoint
import EtaleFundamentalGroups.ContinuousActions.RestrictionEssentialImage
import Mathlib.CategoryTheory.EssentialImage

/-!
# Generic fibers and the kernel of the generic absolute Galois map

The absolute Galois action on a generic fiber is restriction of the action
of the fundamental group. A finite continuous absolute Galois action comes
from a finite étale cover precisely when the generic kernel acts trivially.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Generic pullback and the finite Galois-set equivalence identify the
absolute Galois action with restriction along the generic Galois map. -/
def genericPullbackContActionIso (X : Scheme.{u}) [IsIntegral X] :
    pullback (X.fromSpecStalk (genericPoint X)) ⋙
        (equivContAction X.functionField (SeparableClosure X.functionField)).functor ≅
      functorToContAction
          (fiber (X.genericExtensionMorphism (AlgebraicClosure X.functionField))) ⋙
        ContAction.res FintypeCat (genericAbsoluteGaloisHom X) := by
  let j := X.fromSpecStalk (genericPoint X)
  let xi := ξ X.functionField (AlgebraicClosure X.functionField)
  let E := ContinuousMonoidHom.toContinuousMonoidHom
    (absoluteGaloisEquivFundamentalGroup X.functionField)
  let R := ContAction.res FintypeCat E
  let F := functorToContAction (fiber (xi ≫ j))
  let p := fundamentalGroupHom j xi
  exact (Functor.isoWhiskerLeft (pullback j)
      (equivContActionExtendedFiberIso X.functionField
        (SeparableClosure X.functionField) (AlgebraicClosure X.functionField))).trans
    ((Functor.associator (pullback j)
      (functorToContAction (fiber xi)) R).symm.trans
    ((Functor.isoWhiskerRight (pullbackContActionIso j xi) R).trans
    ((Functor.associator F (ContAction.res FintypeCat p) R).trans
      (Functor.isoWhiskerLeft F (ContAction.resComp FintypeCat E p).symm))))

/-- A finite continuous absolute Galois action occurs as the generic fiber
of a finite étale cover exactly when the generic Galois kernel acts trivially. -/
theorem genericPullback_essImage_iff_ker_le_ker_ρAut
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (Y : ContAction FintypeCat.{u}
      (SeparableClosure X.functionField ≃ₐ[X.functionField]
        SeparableClosure X.functionField)) :
    (pullback (X.fromSpecStalk (genericPoint X)) ⋙
      (equivContAction X.functionField (SeparableClosure X.functionField)).functor).essImage Y ↔
        (genericAbsoluteGaloisHom X).toMonoidHom.ker ≤ (Action.ρAut Y.obj).ker := by
  rw [Functor.essImage_eq_of_natIso (genericPullbackContActionIso X)]
  rw [Functor.essImage_comp_apply_of_essSurj]
  exact ContAction.essImage_res_iff_ker_le_ker_ρAut
    (genericAbsoluteGaloisHom X) (genericAbsoluteGaloisHom_surjective X) Y

/-- A finite étale scheme over the function field extends to the base
exactly when the generic kernel acts trivially on its finite Galois set. -/
theorem genericPullback_obj_essImage_iff_ker_le_ker_ρAut
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (W : FiniteEtale (Spec (.of X.functionField))) :
    (pullback (X.fromSpecStalk (genericPoint X))).essImage W ↔
      (genericAbsoluteGaloisHom X).toMonoidHom.ker ≤
        (Action.ρAut
          (((equivContAction X.functionField (SeparableClosure X.functionField)).functor.obj
            W).obj)).ker := by
  let E := (equivContAction X.functionField (SeparableClosure X.functionField)).functor
  rw [← genericPullback_essImage_iff_ker_le_ker_ρAut X (E.obj W)]
  constructor
  · rintro ⟨Z, ⟨e⟩⟩
    exact ⟨Z, ⟨E.mapIso e⟩⟩
  · rintro ⟨Z, ⟨e⟩⟩
    exact ⟨Z, ⟨E.preimageIso e⟩⟩

end AlgebraicGeometry.FiniteEtale
