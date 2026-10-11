/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Differentials.Kaehler.Weil
import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Cohomology.Cech.DivisorSections
import AlgebraicCurves.Cohomology.SerrePairing
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.Cohomology.Cech.Maps
import AlgebraicCurves.Differentials.Residues.FibreIdentity
import AlgebraicCurves.Cohomology.SerrePairing_pullbackAlong_eq_serrePairing_traceAlong
import AlgebraicCurves.Cohomology.SerrePairing_traceAlong_eq_serrePairing_pullbackAlong
import AlgebraicCurves.Cohomology.SerrePairing_eq_of_cechH1ToH1_eq

/-!
# Serre Pairing trace Along eq serre Pairing trace Along pullback Along of cech H1To H1 eq
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.SerrePairingTraceCompatibility

open KaehlerDifferential

open AlgebraicCurve

end AlgebraicCurves.Cohomology.Proofs.SerrePairingTraceCompatibility

section PublicStatement

open _root_.KaehlerDifferential
open _root_.AlgebraicCurve
open _root_.AlgebraicCurves.Cohomology.Proofs.SerrePairingTraceCompatibility

namespace AlgebraicCurve

theorem serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq
    {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [Nontrivial Ω[F'⁄K]] [IsCurveOver K F']
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φα φβ : F →ₐ[K] F') (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral)
    (htrα : TraceIntegralAlong φα hφα) (hsepβ : SeparableAlong K φβ)
    (hfibα : FibreResidueIdentityAlong φα hφα) (hfibβ : FibreResidueIdentityAlong φβ hφβ)
    {S₀ S₁ T₀ T₁ : Set (Place K F)} (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (ω : ↥(regularDifferentials K F))
    (hωα : Differential.pullbackAlong φα (ω : Ω[F⁄K]) ∈ regularDifferentials K F')
    (hωβα : Differential.traceAlong φβ (Differential.pullbackAlong φα (ω : Ω[F⁄K])) ∈
      regularDifferentials K F)
    (y : cechH1 T₀ T₁ (0 : Divisor K F))
    (x' : cechH1 ((Place.restrictAlong φα hφα) ⁻¹' S₀) ((Place.restrictAlong φα hφα) ⁻¹' S₁) (0 :
      Divisor K F'))
    (hx' : cechH1ToH1 (preimage_restrictAlong_union_eq_univ φα hφα hS) 0 x' =
      cechH1ToH1 (preimage_restrictAlong_union_eq_univ φβ hφβ hT) 0 (cechH1.pullbackAlong φβ hφβ
        T₀ T₁ y)) :
    serrePairing hRT hS ω (cechH1.traceAlong φα hφα htrα S₀ S₁ x')
      = serrePairing hRT hT
          ⟨Differential.traceAlong φβ (Differential.pullbackAlong φα (ω : Ω[F⁄K])), hωβα⟩ y := by
  rw [← serrePairing_pullbackAlong_eq_serrePairing_traceAlong hRT hRT' φα hφα htrα hfibα hS ω hωα
    x',
    serrePairing_eq_of_cechH1ToH1_eq hRT' _ _ ⟨_, hωα⟩ x' _ hx',
    ← serrePairing_traceAlong_eq_serrePairing_pullbackAlong hRT hRT' φβ hφβ hsepβ hfibβ hT ⟨_,
      hωα⟩ hωβα y]

end AlgebraicCurve

end PublicStatement
end ProofImplementation
