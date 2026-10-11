/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Subcanonicity of the étale sites

The big étale topology is coarser than the subcanonical fppf topology.
The inclusion of the small étale site into the slice of the big site is
fully faithful, preserves finite limits, and preserves covering sieves.
Consequently its representable presheaves are sheaves as well.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace EtaleCohomology

/-- Representable presheaves on the big étale site are sheaves, by fppf descent. -/
instance etaleTopology_subcanonical : Scheme.etaleTopology.{u}.Subcanonical := by
  apply GrothendieckTopology.Subcanonical.of_le (K := Scheme.fppfTopology)
  apply Scheme.grothendieckTopology_monotone
  intro X Y f hf
  have : Etale f := hf
  exact ⟨inferInstance, inferInstance⟩

/-- Representable presheaves on the small étale site are sheaves. -/
instance smallEtaleTopology_subcanonical (X : Scheme.{u}) :
    X.smallEtaleTopology.Subcanonical := by
  have : (Scheme.Etale.forget X).LocallyCoverDense (Scheme.etaleTopology.over X) :=
    inferInstanceAs ((MorphismProperty.Over.forget
      (show MorphismProperty Scheme.{u} from @Etale) ⊤ X).LocallyCoverDense _)
  have : RepresentablyFlat (Scheme.Etale.forget X) := flat_of_preservesFiniteLimits _
  have : (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology
      (Scheme.etaleTopology.over X) :=
    Functor.isContinuous_iff_coverPreserving.mpr
      ((Scheme.Etale.forget X).coverPreserving_restrictedTopology (Scheme.etaleTopology.over X))
  exact GrothendieckTopology.subcanonical_of_full_of_faithful
    (Scheme.Etale.forget X) X.smallEtaleTopology (Scheme.etaleTopology.over X)

end EtaleCohomology
