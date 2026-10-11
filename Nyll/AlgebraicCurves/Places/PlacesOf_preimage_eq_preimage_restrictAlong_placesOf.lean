/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_placesOf_preimage_eq_preimage_restrictAlong_placesOf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Places
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Places.PlacesOf_preimage_subset_preimage_restrictAlong_placesOf
import Nyll.AlgebraicCurves.Places.Preimage_restrictAlong_placesOf_subset_placesOf_preimage

/-!
# Places Of preimage eq preimage restrict Along places Of
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.PlacesOf_preimage_eq_preimage_restrictAlong_placesOf

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem _root_.AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [IsSeparated cX] [SmoothOfRelativeDimension 1 cX]
    [IsProper cY] [SmoothOfRelativeDimension 1 cY]
    (π : Y ⟶ X) [UniversallyClosed π]
    (φ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      X.functionField →ₐ[K] Y.functionField)
    (hφ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      φ.toRingHom.IsIntegral)
    (hφπ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    placesOf cY (π ⁻¹ᵁ U) = (Place.restrictAlong φ hφ) ⁻¹' placesOf cX U :=
  Set.Subset.antisymm (AlgebraicCurve.placesOf_preimage_subset_preimage_restrictAlong_placesOf cX
    cY π φ hφ hφπ U)
    (AlgebraicCurve.preimage_restrictAlong_placesOf_subset_placesOf_preimage cX cY π φ hφ hφπ U)
end AlgebraicCurves.Places.Proofs.PlacesOf_preimage_eq_preimage_restrictAlong_placesOf
end ProofImplementation
