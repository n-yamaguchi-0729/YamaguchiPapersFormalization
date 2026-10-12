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

import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
# Pullback of degree-zero divisor classes

The pullback of divisors descends to the degree-zero Picard group.
-/

noncomputable section

namespace AlgebraicCurve.Pic0

open Divisor

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
variable (hFI : FundamentalIdentityAlong K φ hφ)

/-- Pull back degree-zero divisors along the given embedding of function fields. -/
def pullbackAlongDegZeroHom :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F') :=
  ((Divisor.pullbackAlong φ hφ).domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.pullbackAlong_mem_degZero φ hφ hFI D.2)

@[simp]
theorem coe_pullbackAlongDegZeroHom (D : Divisor.degZero (K := K) (F := F)) :
    (pullbackAlongDegZeroHom φ hφ hFI D : Divisor K F') =
      Divisor.pullbackAlong φ hφ (D : Divisor K F) :=
  rfl

/-- The induced pullback homomorphism on degree-zero divisor classes. -/
def pullbackAlongHom : Pic0 K F →+ Pic0 K F' :=
  QuotientAddGroup.map _ _ (pullbackAlongDegZeroHom φ hφ hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pullbackAlong φ hφ hD)

theorem pullbackAlongHom_mk (D : Divisor.degZero (K := K) (F := F)) :
    pullbackAlongHom φ hφ hFI (mk D) = mk (pullbackAlongDegZeroHom φ hφ hFI D) :=
  rfl

end AlgebraicCurve.Pic0
