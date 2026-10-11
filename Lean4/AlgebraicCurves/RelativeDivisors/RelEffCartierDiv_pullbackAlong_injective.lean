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

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_injective_of_flat_of_surjective

/-!
Injectivity of pullback of relative effective Cartier divisors.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_pullbackAlong_injective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_injective
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) [Flat φ] [Surjective φ] :
    Function.Injective fun D : RelEffCartierDiv f r g' => D.pullbackAlong φ hφ := by
  intro D E h
  have hI := congrArg RelEffCartierDiv.I h
  change D.I.comap (mapOnProdOver f φ hφ) = E.I.comap (mapOnProdOver f φ hφ) at hI
  have : Flat (mapOnProdOver f φ hφ) :=
    MorphismProperty.of_isPullback (isPullback_mapOnProdOver f φ hφ).flip inferInstance
  have : Surjective (mapOnProdOver f φ hφ) :=
    MorphismProperty.of_isPullback (isPullback_mapOnProdOver f φ hφ).flip inferInstance
  exact RelEffCartierDiv.ext
    (Scheme.IdealSheafData.comap_injective_of_flat_of_surjective (mapOnProdOver f φ hφ) hI)
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_pullbackAlong_injective
end ProofImplementation
