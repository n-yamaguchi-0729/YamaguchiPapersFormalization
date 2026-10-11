/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Sections on the empty étale scheme

The empty sieve covers an empty étale object. Its sheaf sections are terminal,
and hence zero in any coefficient category with zero morphisms.
-/

universe u v w

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Sections of an étale sheaf over an empty object form a zero object. -/
lemma etaleSections_isZero_of_isEmpty
    {X : Scheme.{u}} (V : X.Etale) [IsEmpty V.left]
    {A : Type v} [Category.{w} A] [HasZeroMorphisms A]
    (F : Sheaf X.smallEtaleTopology A) : IsZero (F.obj.obj (op V)) := by
  have hb : (⊥ : Sieve V) ∈ X.smallEtaleTopology V := by
    change (⊥ : Sieve V) ∈ X.smallGrothendieckTopology
      (show MorphismProperty Scheme from @Etale) V
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X le_rfl]
    apply (Scheme.mem_toGrothendieck_smallPretopology
      (P := show MorphismProperty Scheme from @Etale)
      (Q := show MorphismProperty Scheme from @Etale) V _).mpr
    intro x
    exact isEmptyElim x
  rw [IsZero.iff_id_eq_zero]
  exact (F.isTerminalOfBotCover V hb).hom_ext _ _

end EtaleCohomology
