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
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Nyll.AlgebraicCurves.Geometry.Schemes.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth_isRegularLocalRing_stalk
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain

/-!
# geometrically Integral of smooth of geometrically Connected
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace geometricallyIntegral_of_smooth_of_geometricallyConnected

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GeomIntKit

theorem isIntegral_of_smooth_of_connectedSpace {K : Type u} [Field K] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of K)) [Smooth t] [ConnectedSpace X] : IsIntegral X := by
  have : LocallyOfFiniteType t := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian t
  exact
    AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
    X fun x => by
      have := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := t) x
      exact IsRegularLocalRing.isDomain _

end GeomIntKit

open GeomIntKit in
theorem _root_.AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  let _ : MorphismProperty.IsStableUnderBaseChange
      (@Smooth : MorphismProperty Scheme.{u}) := smooth_isStableUnderBaseChange
  have : Smooth (pullback.snd f y) := by infer_instance
  have : ConnectedSpace ↥(pullback f y) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f y)
  have : IsIntegral (pullback f y) := isIntegral_of_smooth_of_connectedSpace (pullback.snd f y)
  exact IsIntegral.of_isIso h.isoPullback.inv
end AlgebraicCurves.Geometry.Curves.Proofs.geometricallyIntegral_of_smooth_of_geometricallyConnected
end ProofImplementation
