/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sieves.Functoriality

/-!
# Base change on small étale sites

Base change preserves finite limits and étale covering sieves. The covering
statement follows from base change on the localized big étale sites, using the
description of the small topology through the forgetful functors to over categories.
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change of an étale scheme along an arbitrary morphism of schemes. -/
def etaleBaseChange : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback (show MorphismProperty Scheme.{u} from @Etale) ⊤ f

instance : PreservesFiniteLimits (etaleBaseChange f) :=
  inferInstanceAs (PreservesFiniteLimits
    (MorphismProperty.Over.pullback (show MorphismProperty Scheme.{u} from @Etale) ⊤ f))

/-- Base change preserves covering sieves for the actual small étale topology. -/
lemma etaleBaseChange_coverPreserving :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (etaleBaseChange f) where
  cover_preserve {U} {S} hS := by
    let : (Scheme.Etale.forget Y).LocallyCoverDense (Scheme.etaleTopology.over Y) :=
      inferInstanceAs ((MorphismProperty.Over.forget
        (show MorphismProperty Scheme.{u} from @Etale) ⊤ Y).LocallyCoverDense _)
    let : (Scheme.Etale.forget X).LocallyCoverDense (Scheme.etaleTopology.over X) :=
      inferInstanceAs ((MorphismProperty.Over.forget
        (show MorphismProperty Scheme.{u} from @Etale) ⊤ X).LocallyCoverDense _)
    change S ∈ (Scheme.Etale.forget Y).restrictedTopology
      (Scheme.etaleTopology.over Y) U at hS
    change S.functorPushforward (etaleBaseChange f) ∈
      (Scheme.Etale.forget X).restrictedTopology
        (Scheme.etaleTopology.over X) ((etaleBaseChange f).obj U)
    rw [CategoryTheory.Functor.mem_restrictedTopology_iff] at hS ⊢
    rw [← Sieve.functorPushforward_comp]
    change S.functorPushforward
        (Scheme.Etale.forget Y ⋙ CategoryTheory.Over.pullback f) ∈
      (Scheme.etaleTopology.over X) _
    rw [Sieve.functorPushforward_comp]
    exact CoverPreserving.cover_preserve
      (GrothendieckTopology.coverPreserving_overPullback Scheme.etaleTopology f) hS

instance : (etaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology := by
  let : RepresentablyFlat (etaleBaseChange f) := flat_of_preservesFiniteLimits _
  exact CategoryTheory.Functor.isContinuous_iff_coverPreserving.mpr
    (etaleBaseChange_coverPreserving f)

end EtaleCohomology
