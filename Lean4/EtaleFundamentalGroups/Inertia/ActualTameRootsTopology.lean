/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameRootsGroupSystem
import ProCGroups.InverseSystems.Basic
import Mathlib.Topology.Order

/-!
# Topology of the SAME actual tame roots limit

The existing roots system already chooses the discrete topology at every
stage. Its existing inverse-limit topology is therefore Hausdorff, and the
existing coordinatewise group operations are continuous.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory ProCGroups.InverseSystems

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- Each actual stage has precisely its already assigned discrete topology. -/
theorem actualFiniteTameRootsSystem_discreteTopology
    (n : Subtype (actualFiniteTameDegreeSet A K L Q)) :
    DiscreteTopology ((actualFiniteTameRootsSystem A K L Q).X n) := ⟨rfl⟩

/-- The SAME actual roots limit is Hausdorff in its existing topology. -/
theorem actualFiniteTameRootsSystem_t2Space :
    T2Space (actualFiniteTameRootsSystem A K L Q).inverseLimit := by
  have stageT2 : ∀ n : Subtype (actualFiniteTameDegreeSet A K L Q),
      T2Space ((actualFiniteTameRootsSystem A K L Q).X n) := by
    intro n
    have stageDiscrete := actualFiniteTameRootsSystem_discreteTopology A K L Q n
    infer_instance
  exact InverseSystem.t2Space_inverseLimit (actualFiniteTameRootsSystem A K L Q)

/-- The SAME actual roots limit has continuous existing group operations. -/
theorem actualFiniteTameRootsSystem_isTopologicalGroup :
    IsTopologicalGroup (actualFiniteTameRootsSystem A K L Q).inverseLimit := by
  have stageGroups : ∀ n : Subtype (actualFiniteTameDegreeSet A K L Q),
      IsTopologicalGroup ((actualFiniteTameRootsSystem A K L Q).X n) := by
    intro n
    have stageDiscrete := actualFiniteTameRootsSystem_discreteTopology A K L Q n
    infer_instance
  exact ProCGroups.InverseSystems.instIsTopologicalGroupInverseLimit
    (actualFiniteTameRootsSystem A K L Q)

end EtaleFundamentalGroups.Inertia
