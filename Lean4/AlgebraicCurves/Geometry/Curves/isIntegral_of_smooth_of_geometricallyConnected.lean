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

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import AlgebraicCurves.Geometry.Schemes.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import AlgebraicCurves.Geometry.Schemes.Smooth_isRegularLocalRing_stalk
import SchemeTheory.RingTheory.RegularLocalDomain

/-!
# is Integral of smooth of geometrically Connected
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs.isIntegral_of_smooth_of_geometricallyConnected

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.isIntegral_of_smooth_of_geometricallyConnected
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    (hsm : Smooth t) (hgc : GeometricallyConnected t)
    (e : Spec (CommRingCat.of k) ⟶ X) (_he : e ≫ t = 𝟙 _) :
    IsIntegral X := by
  have := hsm
  have := hgc
  have : LocallyOfFiniteType t := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian t
  have : ConnectedSpace X := by
    exact GeometricallyConnected.connectedSpace_of_subsingleton t
  exact
    AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk X
    fun x => by
      have := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := t) x
      exact IsRegularLocalRing.isDomain _
end AlgebraicCurves.Geometry.Curves.Proofs.isIntegral_of_smooth_of_geometricallyConnected
end ProofImplementation
