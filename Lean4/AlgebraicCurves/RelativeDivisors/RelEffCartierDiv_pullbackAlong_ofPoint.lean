/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint

/-!
# Base change of the divisor of a section

Relates pullback of the divisor of a section to the divisor of the pulled back section.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_pullbackAlong_ofPoint

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
namespace OfPointNaturality
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}

theorem isPullback_graphOver_comp [IsSeparated f] (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ])) φ
      (mapOnProdOver f φ hφ) (graphOver f a ha) := by
  have s : IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) ≫ pullback.snd f g)
      φ φ (graphOver f a ha ≫ pullback.snd f g') := by
    rw [graphOver_snd, graphOver_snd]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine IsPullback.of_right s ?_ (isPullback_mapOnProdOver f φ hφ).flip
  apply pullback.hom_ext <;> simp

end AlgebraicGeometry.RelEffCartierDiv.OfPointNaturality

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_ofPoint {𝒞 S : Scheme.{u}} (f :
  𝒞 ⟶ S) [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : T' ⟶ 𝒞) (ha : a ≫ f = g') (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (RelEffCartierDiv.ofPoint f a ha).pullbackAlong φ hφ =
      RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) := by
  refine RelEffCartierDiv.ext ?_
  change (graphOver f a ha).ker.comap (mapOnProdOver f φ hφ) = (graphOver f (φ ≫ a) _).ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (AlgebraicGeometry.RelEffCartierDiv.OfPointNaturality.isPullback_graphOver_comp
      f a ha φ hφ).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_pullbackAlong_ofPoint
end ProofImplementation
