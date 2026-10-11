/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.SubalgebraPreimage
import ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Roots in the normalization residue field

Defines the native group object of roots of a fixed degree in the original normalization residue
field.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The full roots of a fixed degree in the original normalization residue
field, retained as its native group object before the field tower appears. -/
def normalizationRootsGroup
    (A : Type u) (L : Type v) [CommRing A] [CommRing L] [Algebra A L]
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat A L)) [Q.IsPrime]
    (n : ℕ) : GrpCat.{v} :=
  RamificationTheory.HilbertRamification.rootsGroupObject Q.ResidueField n

end EtaleFundamentalGroups.Inertia

end
