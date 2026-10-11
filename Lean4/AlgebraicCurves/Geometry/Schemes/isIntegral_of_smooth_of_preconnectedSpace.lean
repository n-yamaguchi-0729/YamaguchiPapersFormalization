/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import AlgebraicCurves.Geometry.Schemes.Smooth_isRegularLocalRing_stalk
import AlgebraicCurves.Geometry.Schemes.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import SchemeTheory.RingTheory.RegularLocalDomain

/-!
# is Integral of smooth of preconnected Space
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.isIntegral_of_smooth_of_preconnectedSpace

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] [PreconnectedSpace X] [Nonempty X] : IsIntegral X := by
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : ConnectedSpace X := { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  exact
    AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk X
    fun x => by
      have := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
      exact IsRegularLocalRing.isDomain _
end AlgebraicCurves.Geometry.Schemes.Proofs.isIntegral_of_smooth_of_preconnectedSpace
end ProofImplementation
