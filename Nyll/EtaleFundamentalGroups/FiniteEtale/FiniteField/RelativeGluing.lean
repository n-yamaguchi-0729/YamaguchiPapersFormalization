/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.FiniteEtale.RelativeGluing

/-!
# Compatibility name for general scheme gluing

The general construction is owned by SchemeTheory; this file retains its
existing finite-field consumer name.
-/

namespace EtaleFundamentalGroups

/-- Compatibility name for the general scheme gluing theorem. -/
alias exists_finiteEtale_gluedToBase :=
  AlgebraicGeometry.Scheme.GlueData.exists_finiteEtale_gluedToBase

end EtaleFundamentalGroups
