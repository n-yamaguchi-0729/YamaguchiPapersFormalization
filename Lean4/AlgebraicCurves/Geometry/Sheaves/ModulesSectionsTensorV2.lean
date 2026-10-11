/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import SchemeTheory.Modules.PresheafInternalHom
import AlgebraicCurves.Foundations.Algebra.SheafOfModules_MonoidalV2
import SchemeTheory.Modules.TensorPowers
import SchemeTheory.Modules.TensorSections

/-!
# Modules Sections Tensor V2
-/

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Hom

variable (L M : X.Modules)

end Hom

section Sections

variable {L M : X.Modules} {U : X.Opens}

end Sections

section Pow

variable {L : X.Modules} {U : X.Opens}

end Pow

section Frame

variable {M : X.Modules} {U : X.Opens}

namespace IsFrameOn

variable {s : Γ(M, U)} {V : X.Opens}

end IsFrameOn

end Frame

end AlgebraicGeometry.Scheme.Modules

end
