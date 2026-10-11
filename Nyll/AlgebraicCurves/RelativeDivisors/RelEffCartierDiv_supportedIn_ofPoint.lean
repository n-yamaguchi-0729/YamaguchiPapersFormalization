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

import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn

/-!
# Rel Eff Cartier Div supported In of Point
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_supportedIn_ofPoint

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.supportedIn_ofPoint
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (U : 𝒞.Opens) (hU : ∀ t : T, a t ∈ U) :
    (RelEffCartierDiv.ofPoint f a ha).SupportedIn U := by
  intro x hx
  have hcl : (closure (Set.range ⇑(graphOver f a ha)) : Set ↥(pullback f g)) = Set.range
    ⇑(graphOver f a ha) :=
    (graphOver f a ha).isClosedEmbedding.isClosed_range.closure_eq
  have hx' : x ∈ Set.range ⇑(graphOver f a ha) := by
    have h2 := hx
    rw [RelEffCartierDiv.ofPoint_I, Scheme.Hom.support_ker] at h2
    rw [← hcl]
    exact h2
  obtain ⟨t, rfl⟩ := hx'
  change pullback.fst f g (graphOver f a ha t) ∈ U
  rw [← Scheme.Hom.comp_apply, graphOver_fst]
  exact hU t
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_supportedIn_ofPoint
end ProofImplementation
