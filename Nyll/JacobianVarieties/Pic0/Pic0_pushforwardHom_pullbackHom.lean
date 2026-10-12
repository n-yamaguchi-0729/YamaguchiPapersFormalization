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

import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Divisors.Divisor_pushforward_pullback_of_finite

/-!
Pullback followed by pushforward on the Picard group is multiplication by the extension degree.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_pushforwardHom_pullbackHom

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Pic0
open _root_.AlgebraicCurve.Pic0
open _root_.AlgebraicCurve.Pic0
open _root_.AlgebraicCurve
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

private theorem pushforwardHom_pullbackHom_s11 [Module.Finite F F'] [SumRamificationInertia K F F']
    (H : Divisor.PushforwardNormFormula K F F') (x : Pic0 K F) :
    pushforwardHom K F F' H (pullbackHom F' x) = (Module.finrank F F' : ℤ) • x := by
  obtain ⟨D, rfl⟩ := mk_surjective x
  rw [pullbackHom_mk, pushforwardHom_mk]
  rw [show ((Module.finrank F F' : ℤ) • mk D : Pic0 K F)
      = mk ((Module.finrank F F' : ℤ) • D) from rfl]
  exact congrArg mk (Subtype.ext (Divisor.pushforward_pullback_of_finite (D : Divisor K F)))

end AlgebraicCurve.Pic0

theorem _root_.AlgebraicCurve.Pic0.pushforwardHom_pullbackHom {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [Module.Finite F F']
    [SumRamificationInertia K F F'] (H : Divisor.PushforwardNormFormula K F F')
    (x : Pic0 K F) : Pic0.pushforwardHom K F F' H (Pic0.pullbackHom F' x) =
    (Module.finrank F F' : ℤ) • x :=
  AlgebraicCurve.Pic0.pushforwardHom_pullbackHom_s11 H x
end JacobianVarieties.Pic0.Proofs.Pic0_pushforwardHom_pullbackHom
end ProofImplementation
