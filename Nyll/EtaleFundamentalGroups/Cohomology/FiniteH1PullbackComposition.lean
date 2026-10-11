/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterComposition
import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterPullback
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison

/-! # Composition for actual finite-coefficient H¹ pullback

This is the composition law for the existing derived-sheaf pullback, obtained
from the faithful character comparison, including its geometric base points.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace EtaleFundamentalGroups.Cohomology

/-- Actual derived finite-coefficient H¹ pullback is contravariantly
compatible with composition of connected scheme morphisms. -/
theorem constantFiniteH1Pullback_comp
    {X Y Z : Scheme} [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A]
    (c : Sheaf.H.{0} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1) :
    constantCohomologyPullback (f ≫ g) A 1 c =
      constantCohomologyPullback f A 1 (constantCohomologyPullback g A 1 c) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  apply h1Character_injective A geom
  apply ContinuousMonoidHom.ext
  intro σ
  have hfg := congrArg (fun χ => χ σ)
    (h1Character_schemePullback (f ≫ g) A geom c)
  have hf := congrArg (fun χ => χ σ)
    (h1Character_schemePullback f A geom (constantCohomologyPullback g A 1 c))
  have hg := congrArg (fun χ => χ (FiniteEtale.fundamentalGroupHom f geom σ))
    (h1Character_schemePullback g A (geom ≫ f) c)
  exact hfg.symm.trans
    ((h1Character_fundamentalGroupHom_comp f g geom A c σ).symm.trans (hg.trans hf))

end EtaleFundamentalGroups.Cohomology
