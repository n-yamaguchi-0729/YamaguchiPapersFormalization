/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.ScalarRestrictionGroupMap
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Restriction to finite Galois group objects

Defines the Galois group object of a finite intermediate field and the restriction homomorphism
from the ambient Galois group.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- The native Galois group of the actual finite intermediate field. -/
def finiteGaloisGroupObject (E : FiniteGaloisIntermediateField K L) : GrpCat.{v} :=
  galoisGroupObject K E

/-- Actual restriction from the original ambient Galois group. -/
def finiteGaloisRestrictionGroupMap (E : FiniteGaloisIntermediateField K L) :
    GrpCat.Hom (galoisGroupObject K L) (finiteGaloisGroupObject K L E) where
  hom' := AlgEquiv.restrictNormalHom E

end EtaleFundamentalGroups.Inertia

end
