/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_correspondence_comm_of_exchange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Divisor_pullbackAlong_pullbackAlong
import Nyll.AlgebraicCurves.Divisors.Divisor_pushforwardAlong_pushforwardAlong
import Nyll.AlgebraicCurves.Divisors.Divisor_pushforwardAlong_pullbackAlong_of_surjective
import Nyll.AlgebraicCurves.Divisors.Divisor_correspondence_congr

/-!
# Divisor correspondence comm of exchange
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_comm_of_exchange
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

namespace AL4Sol

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [HasPrincipalDivisors K F']

theorem comm_of_exchange (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ :
  ψ.toRingHom.IsIntegral)
    (g : F' →ₐ[K] F') (hg : g.toRingHom.IsIntegral) (hgs : Function.Surjective g)
    (h1 : g.comp φ = ψ) (h2 : g.comp ψ = φ) :
    Divisor.correspondence φ ψ hφ hψ = Divisor.correspondence ψ φ hψ hφ := by
  have hgψ : (g.comp ψ).toRingHom.IsIntegral := by rw [h2]; exact hφ
  have hgφ : (g.comp φ).toRingHom.IsIntegral := by rw [h1]; exact hψ
  refine AddMonoidHom.ext (fun D => ?_)
  rw [Divisor.correspondence_congr h2.symm h1.symm hφ hψ hgψ hgφ D]
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply]
  rw [← Divisor.pullbackAlong_pullbackAlong ψ g hψ hg hgψ D]
  rw [← Divisor.pushforwardAlong_pushforwardAlong φ g hφ hg hgφ]
  rw [Divisor.pushforwardAlong_pullbackAlong_of_surjective g hg hgs]

end AL4Sol

theorem _root_.AlgebraicCurve.Divisor.correspondence_comm_of_exchange {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
  (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (g : F' →ₐ[K] F') (hg :
  g.toRingHom.IsIntegral) (hgs : Function.Surjective g) (h1 : g.comp φ = ψ) (h2 : g.comp ψ = φ) :
  AlgebraicCurve.Divisor.correspondence φ ψ hφ hψ = AlgebraicCurve.Divisor.correspondence ψ φ hψ hφ
  :=
  AL4Sol.comm_of_exchange φ ψ hφ hψ g hg hgs h1 h2
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_comm_of_exchange
end ProofImplementation
