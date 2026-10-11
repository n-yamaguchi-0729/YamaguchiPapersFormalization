/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.InverseLimitStages
import SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity

/-!
# Coherence of the actual stage cocone

The cartesian stage transitions respect the canonical identity and
composition isomorphisms of pullback.  Applying the localization functor
therefore gives the actual coherent cocone used in its 2-colimit
presentation.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale.InverseLimitModel

universe u v w

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable {J : Type v} [Category.{w} J] (F : J ⥤ Scheme.{u})

/-- The two successive cartesian transitions agree with the transition of
the composite after the canonical pullback-composition comparison. -/
theorem transition_comp_app {i j k : J} (a : i ⟶ j) (b : j ⟶ k)
    (A : FiniteEtale (F.obj k)) :
    (stageInclusion F i).map
        ((MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤)
          (F.map a) (F.map b) (F.map (a ≫ b)) (F.map_comp a b)).hom.app A) ≫
      (transition F a).app ((pullback (F.map b)).obj A) ≫
      (transition F b).app A = (transition F (a ≫ b)).app A := by
  apply MorphismProperty.Comma.Hom.ext
  · exact pullbackComp_hom_app_left_fst_fst (F.map a) (F.map b)
      (F.map (a ≫ b)) (F.map_comp a b) A
  · exact Category.id_comp (a ≫ b)

/-- The cartesian transition over an identity is the actual pullback
identity comparison, including the diagram's map-id equality. -/
theorem transition_id_app (i : J) (A : FiniteEtale (F.obj i)) :
    (transition F (𝟙 i)).app A =
      (stageInclusion F i).map
        ((MorphismProperty.Over.pullbackCongr
            (P := @IsFiniteEtale) (Q := ⊤) (F.map_id i) ≪≫
          pullbackIdIso (F.obj i)).hom.app A) := by
  apply MorphismProperty.Comma.Hom.ext
  · exact (MorphismProperty.Over.pullbackCongr_hom_app_left_fst
      (P := @IsFiniteEtale) (Q := ⊤) (F.map_id i) A).symm
  · rfl

end AlgebraicGeometry.FiniteEtale.InverseLimitModel
