/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Trace.Defs

/-!
# Trace
-/

noncomputable section

namespace AlgebraicCurve

variable (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F']

/-- Compatibility of a differential trace map with the field trace on scalar multiples. -/
def IsTraceDiff (t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]) : Prop :=
  ∀ (y : F') (ω : Ω[F⁄K]),
    t (y • KaehlerDifferential.map K K F F' ω) = Algebra.trace F F' y • ω

open scoped Classical in
/-- A differential trace map when one exists, and the zero map otherwise. -/
def traceDiff : Ω[F'⁄K] →ₗ[F] Ω[F⁄K] :=
  if h : ∃ t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K], IsTraceDiff K F F' t then h.choose else 0

end AlgebraicCurve
