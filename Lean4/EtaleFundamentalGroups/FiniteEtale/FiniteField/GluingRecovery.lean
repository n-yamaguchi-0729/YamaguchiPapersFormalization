/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import SchemeTheory.Gluing.Recovery

/-!
# Compatibility name for general scheme gluing

The general construction is owned by SchemeTheory; this file retains its
existing finite-field consumer name.
-/

namespace EtaleFundamentalGroups

/-- Compatibility name for the general scheme gluing theorem. -/
alias exists_glueData_iso_of_overlap :=
  AlgebraicGeometry.Scheme.GlueData.exists_glueData_iso_of_overlap

end EtaleFundamentalGroups
