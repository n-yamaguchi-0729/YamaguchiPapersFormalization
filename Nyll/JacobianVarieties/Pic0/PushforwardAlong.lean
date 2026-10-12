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
# Pushforward of degree-zero divisor classes

The pushforward of divisors descends to the degree-zero Picard group.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem Place.deg_restrictAlong_mul_inertiaDegAlong (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  let halgebraAlong := algebraAlong φ
  have htowerAlong := isScalarTower_along φ
  have hintegralAlong := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg

namespace Pic0

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
variable (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)

/-- Push forward degree-zero divisors along the given embedding of function fields. -/
def pushforwardAlongDegZero :
    Divisor.degZero (K := K) (F := F') →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.pushforwardAlong φ hφ).domRestrict
    (Divisor.degZero (K := K) (F := F'))).codRestrict _
    (fun D => Divisor.pushforwardAlong_mem_degZero φ hφ D.2)

@[simp]
theorem coe_pushforwardAlongDegZero (D : Divisor.degZero (K := K) (F := F')) :
    (pushforwardAlongDegZero φ hφ D : Divisor K F) =
      Divisor.pushforwardAlong φ hφ (D : Divisor K F') :=
  rfl

/-- The induced pushforward homomorphism on degree-zero divisor classes. -/
def pushforwardAlongHom : Pic0 K F' →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (pushforwardAlongDegZero φ hφ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforwardAlong φ hφ hfin hN hD)

theorem pushforwardAlongHom_mk (D : Divisor.degZero (K := K) (F := F')) :
    pushforwardAlongHom φ hφ hfin hN (mk D) = mk (pushforwardAlongDegZero φ hφ D) :=
  rfl

end Pic0

end AlgebraicCurve
