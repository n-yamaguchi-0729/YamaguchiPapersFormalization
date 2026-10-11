/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.Gluing.CommonCover

/-!
# Compatibility names for relative cover recovery

The general constructions live in SchemeTheory.
-/

namespace EtaleFundamentalGroups

/-- Compatibility name for the general cover-recovery theorem. -/
alias exists_iso_of_common_open_cover :=
  AlgebraicGeometry.Scheme.Cover.exists_iso_of_common_open_cover

/-- Compatibility name for the general cover-recovery theorem. -/
alias isPullback_of_cartesian_chart_overlap :=
  AlgebraicGeometry.Scheme.Cover.isPullback_of_cartesian_chart_overlap

end EtaleFundamentalGroups
