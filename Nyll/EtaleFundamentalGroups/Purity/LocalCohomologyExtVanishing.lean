/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Local-cohomology vanishing from Ext vanishing

Local cohomology is defined as a colimit of Ext modules.  This file records
the categorical passage from pointwise vanishing of the Ext diagram to
vanishing of the resulting local-cohomology module.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

/-- A local-cohomology module vanishes if every Ext module in its defining
ideal-powers diagram vanishes. -/
theorem localCohomology_isZero_of_subsingleton_ext_powers
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (hExt : ∀ n : ℕ, Subsingleton
      (((_root_.Ext R (ModuleCat.{u} R) i).obj
        (op (ModuleCat.of R (R ⧸ I ^ n)))).obj M)) :
    IsZero ((localCohomology I i).obj M) := by
  let F := localCohomology.diagram (localCohomology.idealPowersDiagram I) i
  let D := F ⋙ (evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj M
  have hD : IsZero D := Functor.isZero D fun n ↦ by
    let N : ModuleCat.{u} R := ModuleCat.of R (R ⧸ I ^ unop (unop n))
    let : Subsingleton
        (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj M) :=
      hExt (unop (unop n))
    change IsZero (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj M)
    exact ModuleCat.isZero_of_subsingleton _
  have hcolimit : IsZero (colimit D) :=
    (colimit.isColimit D).isZero_pt hD
  change IsZero ((colimit F).obj M)
  exact hcolimit.of_iso <| colimitObjIsoColimitCompEvaluation F M

end EtaleFundamentalGroups

end
