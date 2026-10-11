/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteGaloisRestrictionGroupMap
import SchemeTheory.Normalization.ScalarRestrictionGroupMap
import Mathlib.FieldTheory.KrullTopology

/-!
# Original Krull topology on native Galois group owners

The native group objects retain exactly Mathlib's original Krull topology.
The finite native owner inherits its already proved discrete Krull topology.
No normalization ring or inertia subgroup is opened in this field-only scope.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- The original Krull topology on the native ambient Galois group. -/
instance galoisGroupObject_topologicalSpace :
    TopologicalSpace (galoisGroupObject K L).carrier := krullTopology K L

instance galoisGroupObject_isTopologicalGroup :
    IsTopologicalGroup (galoisGroupObject K L).carrier :=
  inferInstanceAs (IsTopologicalGroup Gal(L/K))

/-- The finite group retains its own original Krull topology. -/
instance finiteGaloisGroupObject_topologicalSpace (E : FiniteGaloisIntermediateField K L) :
    TopologicalSpace (finiteGaloisGroupObject K L E).carrier := krullTopology K E

instance finiteGaloisGroupObject_discreteTopology (E : FiniteGaloisIntermediateField K L) :
    DiscreteTopology (finiteGaloisGroupObject K L E).carrier :=
  krullTopology_discreteTopology_of_finiteDimensional K E

end EtaleFundamentalGroups.Inertia

end
